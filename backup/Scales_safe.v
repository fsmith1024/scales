Module Scales.

(** * Introduction

This module defines a small logic for reasoning about problems with
balance scales.  These kinds of problems make good brainteasers.  For
example, if you have twelve coins, and you know one of them is a
forgery.  All the real coins weigh the same, and the forgery does not.
If the only tool you have is a balance scale, how many times must you
use it to find the forgery?

There are many variations on these kinds of problems that vary in the
number of fakes in the set, and the information that is known about
them.  For example, you may or may not know that the fake is lighter
or heavier than the real coins.
*)

Require Import Bool.
Require Import Arith.
Require Import List.
Require Import ListSet.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Import ListNotations.

(** * Encoding sets of coins

We encode sets of coins as a list of coins which are either fake coins
or gold coins. *)

Inductive coin := gold | fake.

Notation coins := (list coin).

Definition coin_weight c :=
  match c with 
    | gold => 2
    | fake => 1
  end.

(** This definition is not ideal.  By this definition we limit our
encoding to problems where we know the reltionship between the weight
of the fake coins and the gold coins.
*)

(* The predicate [[exactlyn]] defines valid sets with a given number
of fake coins. *)

Inductive exactlyn : nat -> coins -> Prop :=
| exactlyn_base : (exactlyn 0 nil)
| exactlyn_fake : (forall n:nat, forall ns:coins, exactlyn n ns -> exactlyn (S n) (fake::ns))
| exactlyn_gold : (forall n:nat, forall ns:coins, exactlyn n ns -> exactlyn n (gold::ns))
.

(** * Encoding weighing

Encoding "usage of the scale" directly in CIC would require some kind
of resource logic (linear logic), we must be more creative.

To solve this problem, we define a small language for encoding the
decision procedure (proc).  A given decision procedure is a finite
tree.  We can count the occurences of "weighings" along any path thus
determining the maximum number of times the scale was used.  And we
can then prove that the given procedure finds the forgery no matter
the input.

*)

(** [[proc]] is the encoding of a decision procedure that takes as input
some [[coins]] and returns those same [[coins]] in a different order.

  - Stop : Stops execution
  - Swap n m p: Swaps the m elements starting at the nth element to the 
    head of the list.
  - Weigh n pLt pEq pGt : Weighs the first n coins against the next n, 
    and then calls the appropriate procedure.

Notice that this language only admits finite programs, and every
program represents a legal set of operations.  
*)
Inductive proc : Set := 
   | Stop  
   | Swap : nat -> nat -> proc -> proc 
   | Weigh : nat -> proc -> proc -> proc -> proc
.

(** To bring [[proc]] to life, we will now implement a semantics fo
the language.  *)

(** ** Swap *)

(** Extract the nth element from a list, and leave the remainder. *)
Fixpoint swap_rec (A: Type) (L: list A)  (n:nat)  (m:nat) : ((list A) * (list A)) := 
  match L,n,m with
  | nil, _,_ =>  (nil,L)
  | _,0,0 => (nil,L)
  | car::cdr,0,S k => (fun p => (car :: (fst p), (snd p))) (swap_rec A cdr 0 k)
  | car::cdr,S n,_ =>  (fun p => (fst p, car :: snd p)) (swap_rec A cdr n m)
end.

(** This is the main definition used by the Swap instruction. *)
Definition swap (A:Type) (L: list A) (n:nat) (m:nat) :=
    ((fun p => ((fst p) ++ (snd p))) (swap_rec A L n m))
.

(** This alternate definition is equivalent. As we will prove later. *)
Definition swap_alt (A:Type) (L:list A) (n:nat) (m:nat) :=
  (firstn m (skipn n L)) ++ (firstn n L) ++ (skipn (n+m) L)
.

(** ** Weigh *)

(** Sum up the weights of a set of coins. *)
Definition coin_sum (cs : coins) : nat := ListSet.set_fold_right plus (List.map coin_weight cs) 0.

Lemma sum_cons: forall L:coins, forall a:coin, coin_sum (a::L) = (coin_weight a) + (coin_sum L).
intro L.
destruct L.
intro a; simpl; auto.
intro a.
unfold coin_sum; unfold set_fold_right.
unfold fold_right.
fold fold_right.
reflexivity.
Qed.

(* Pick the first n elements of the list *)
Fixpoint pick_rec (A:Type) (n:nat) (L : list A) : (list A * list A) :=
   match L,n with
   | nil,_ => (nil,nil)
   | _,0 => (nil,L)
   | car::cdr,(S n) => 
       (fun p => ((car :: (fst p)), snd p)) (pick_rec A n cdr)
end.

Definition weigh (n:nat) (L : coins) :=
    let (a,rest) := pick_rec coin n L in
    let (b,rest2) := pick_rec coin n rest in
    nat_compare (coin_sum a) (coin_sum b)
.

(** ** Evaluation *)

(* Evaluate a weighing procedure.  Given a set of coins this returns a reordered
set.  We consider this a solution if the fake coin is at the head of the list. *)
Fixpoint procEval (p: proc) (g: coins) : coins  :=
match p with
| Stop => g
| Swap n m p => (procEval p (swap coin g n m))
| Weigh n plt peq pgt => 
  (match weigh n g with
  | Lt => (procEval plt g)
  | Eq => (procEval peq g)
  | Gt => (procEval pgt g)
  end)
end.

(** * Properties of Interest *)

(* Count the number of uses of a scale in a procedure. *)
Fixpoint procCost (p:proc) : nat :=
  match p with
  | Stop => 0
  | Swap _ _ p => procCost p
  | Weigh _  p1 p2 p3 => 1 + max (procCost p1) (max (procCost p2) (procCost p3))
  end.

(* Maximum size stack this program can observe. *)
Fixpoint procDepth (p:proc) : nat :=
  (match p with 
  | Stop => 0
  | Swap n m p => max (n+m) (procDepth p)
  | Weigh n p1 p2 p3 => max (n + n) (max (max (procDepth p1) (procDepth p2)) (procDepth p3))
  end).


(** * Correctness 

For [[proc]] to be a valid encoding of this problem it is important
that procedures cannot manufacture coins or otherwise cheat.  To
encode this correctness criteria we prove that the output is always a
permutation of the input.

*)

Require Import Permutation.

Lemma swap_permutes: forall L:coins, forall k m:nat, Permutation L (swap coin L k m).
intro L.
induction L.
unfold swap; simpl.
unfold swap_rec;simpl.
reflexivity.
intro k.
induction k.
induction m.
unfold swap; simpl; reflexivity.
unfold swap; simpl.
assert ((fst (swap_rec coin L 0 m) ++ snd (swap_rec coin L 0 m)) = (swap coin L 0 m)).
unfold swap; reflexivity.
rewrite H.
apply Permutation_cons.
apply IHL.
induction m.
unfold swap; simpl.
apply Permutation_cons_app.
apply IHL.
unfold swap; simpl.
apply Permutation_cons_app.
apply IHL.
Qed.

Lemma exactlyn_permutes: forall (nsl  nsl' : coins), (Permutation nsl nsl') ->
    forall n:nat, exactlyn n nsl -> exactlyn n nsl'.
intros nsl nsl'.
intro H.
induction H.
trivial.
intro n.
inversion 1.
apply exactlyn_fake.
apply IHPermutation.
exact H3.
apply exactlyn_gold.
apply IHPermutation.
exact H3.
intro n.
inversion 1.
rewrite <- H0 in H.
rewrite <- H1 in H.
inversion H2.
apply exactlyn_fake.
apply exactlyn_fake.
exact H6.
apply exactlyn_gold.
apply exactlyn_fake.
exact H6.
inversion H2.
constructor.
constructor.
exact H6.
constructor;constructor.
exact H6.
intros.
apply IHPermutation2.
apply IHPermutation1.
exact H1.
Qed.

Lemma procEval_permutes: forall p:proc, forall L : coins, Permutation L  (procEval p L).
intro p.
induction p.
simpl; reflexivity.
simpl.
intro L.
assert (Permutation L (swap coin L n n0)).
apply swap_permutes.
symmetry.
apply Permutation_trans with (l' := (swap coin L n n0)).
symmetry.
apply IHp.
symmetry.
exact H.
unfold procEval; simpl.
fold procEval.
intro L.
case (weigh n L).
apply IHp2.
apply IHp1.
apply IHp3.
Qed.


(** * Example with 4 and 12 coins *)

(* Given 4 coins where one is fake.  Find the fake one. [[p4]
encodes a solution to this problem.  We will prove this below.  *)
Definition p4: proc := 
   (Weigh 1 
       Stop 
        (Swap 2 2 (Weigh 1 Stop Stop (Swap 1 1 Stop)))
        (Swap 1 1 Stop)).

Example p4Example1: procEval p4 [gold;gold;fake;gold] = [fake;gold;gold;gold].
compute.
reflexivity.
Qed.

(* Given twelve coins where one is lighter, Find the lighter one
[[p12]] is a solution to this problem as we will prove below.  *)
Definition p12 : proc := 
    (Weigh 4
        p4
         (Swap 8 4 p4)
         (Swap 4 4 p4)).

(* Examples used to test our "solutions". *)
Definition ex1 : coins := [gold;gold;gold;gold; gold;gold;gold;gold; gold;gold;gold;fake].
Definition ex2 : coins := [gold;fake;gold;gold; gold;gold;gold;gold; gold;gold;gold;gold].
Definition ex3 : coins := [gold;gold;gold;gold; gold;gold;fake;gold; gold;gold;gold;gold].


(* Now we verify that everything worka. *)
Eval cbv in (procEval p12 ex1).
Eval cbv in (procEval p12 ex2).
Eval cbv in (procEval p12 ex3).

Eval simpl in (procCost p12).

Lemma procEval_length: forall p:proc, forall L:coins, (length L) = (length (procEval p L)).
intros p L.
apply Permutation_length.
apply procEval_permutes.
Qed.

Lemma firstn_length: forall A:Type, forall L1 L2 : (list A), (firstn (length L1) (L1 ++ L2)) = L1.
intros A L1 L2.
induction L1.
simpl; reflexivity.
simpl.
f_equal.
exact IHL1.
Qed.

Lemma app_cons_ignore: forall A:Type, forall L11 L12 L21  L22 : (list A), forall a : A, (length L11 = length L21) -> (L11 ++ L12 = L21 ++ L22) -> (L11 ++ (a::L12) = L21 ++ (a::L22)).
intros A L11 L12 L21 L22 a.
intro Hlen.
intro Happ.
f_equal.
rewrite <- (firstn_length A L11 L12).
rewrite <- (firstn_length A L21 L22).
rewrite Hlen.
rewrite Happ.
reflexivity.
f_equal.
apply (app_inv_head L11 _ _).
rewrite <- (firstn_length _ L11 L12) at 2.
rewrite Hlen.
rewrite Happ at 2.
rewrite firstn_length.
exact Happ.
Qed.

Lemma skipn_length: forall A:Type, forall L : (list A), forall n:nat, length(skipn n L) = (length L) - n.
intros A L.
induction L.
simpl.
destruct n.
simpl; reflexivity.
simpl; reflexivity.
induction n.
simpl; reflexivity.
simpl.
apply IHL.
Qed.

Lemma swap_rec_fst_len: forall A:Type, forall L:list A, forall n m:nat, (length (fst (swap_rec A L n m))) = (min ((length L)-n) m).
intros A L.
induction L.
simpl; reflexivity.
induction n.
induction m.
simpl; reflexivity.
simpl.
f_equal.
replace (length L) with ((length L) - 0).
apply IHL.
rewrite minus_n_O.
reflexivity.
induction m.
simpl.
apply IHL.
simpl.
apply IHL.
Qed.

Lemma swap_equiv: forall A:Type, forall L: list A, forall n m:nat, (swap A L n m) = (swap_alt A L n m).
intros A L.
induction L.
unfold swap; unfold swap_alt.
simpl.
destruct n.
simpl.
destruct m.
simpl; reflexivity.
simpl; reflexivity.
destruct m.
simpl;reflexivity.
simpl;reflexivity.
unfold swap; unfold swap_alt.
induction n.
simpl.
induction m.
simpl; reflexivity.
simpl.
f_equal.
apply IHL.
simpl.
intro m.
apply app_cons_ignore.
rewrite swap_rec_fst_len.
rewrite List.firstn_length.
rewrite Min.min_comm at 1.
f_equal.
rewrite skipn_length.
reflexivity.
apply IHL.
Qed.

Lemma swap_tl: forall A: Type, forall Lhd Ltl : (list A), forall n m : nat, 
    ((n+m) <= length Lhd) -> (swap A (Lhd ++ Ltl) n m) = (swap A Lhd n m) ++ Ltl. 
intros A Lhd.
induction Lhd.
simpl.
intros Ltl n m.
intro Hlen.
apply le_n_0_eq in Hlen.
symmetry in Hlen.
apply plus_is_O in Hlen.
elim Hlen.
intros n0 m0.
rewrite n0; rewrite m0.
unfold swap.
case Ltl.
simpl;reflexivity.
simpl;reflexivity.
intros Ltl n m.
induction n.
simpl.
induction m.
intro.
unfold swap; unfold swap_rec.
simpl; reflexivity.
intro Hlen.
unfold swap; unfold swap_rec.
fold swap_rec.
simpl.
f_equal.
apply (IHLhd Ltl 0 m).
simpl.
 apply le_S_n.
exact Hlen.
intro Hlen.
unfold swap; unfold swap_rec.
fold swap_rec.
simpl.
assert ((n+m) <= length Lhd).
apply le_S_n.
rewrite <- plus_Sn_m.
replace (S (length Lhd)) with (length (a::Lhd)).
exact Hlen.
simpl;reflexivity.
rewrite <- app_assoc.
simpl.
apply app_cons_ignore.
rewrite swap_rec_fst_len.
rewrite swap_rec_fst_len.
replace (min (length (Lhd ++ Ltl) - n) m) with m.
replace (min (length Lhd - n) m) with m.
reflexivity.
symmetry.
apply Min.min_r.
apply NPeano.Nat.le_add_le_sub_r.
rewrite plus_comm.
exact H.
symmetry.
apply Min.min_r.
apply NPeano.Nat.le_add_le_sub_r.
rewrite app_length.
apply le_plus_trans.
rewrite plus_comm.
exact H.
unfold swap in IHLhd.
rewrite app_assoc.
apply (IHLhd Ltl n m).
exact H.
Qed.

Lemma skipn_app: 
  forall A:Type, forall L1 L2 : list A,
    (skipn (length L1) (L1 ++ L2)) = L2.
intros A L1.
induction L1.
simpl.
tauto.
simpl.
apply IHL1.
Qed.

Lemma firstn_id:
  forall A:Type, forall L : list A,
    (firstn (length L) L) = L.
intros A L.
induction L.
simpl.
reflexivity.
simpl.
f_equal.
apply IHL.
Qed.

Lemma swap_app: 
  forall A:Type, forall L1 L2:list A, 
    swap A (L1 ++ L2) (length L1) (length L2) = (L2 ++ L1).
intros A L1 L2.
rewrite swap_equiv.
unfold swap_alt.
rewrite skipn_app.
rewrite firstn_id.
rewrite app_assoc.
rewrite firstn_length.
rewrite<- app_length.
rewrite<- (app_nil_r (L1 ++ L2)) at 2. 
rewrite skipn_app.
rewrite app_nil_r.
reflexivity.
Qed.

Lemma fst_pick_rec: 
  forall A:Type, forall L : list A, forall n:nat,
    length L = n -> fst(pick_rec A n L) = L.
intros A L.
induction L.
intros n Hlen.
simpl in Hlen.
rewrite <- Hlen.
simpl.
reflexivity.
intro n.
intro Hlen.
simpl in Hlen.
rewrite<- Hlen.
simpl.
f_equal.
apply IHL.
reflexivity.
Qed.
 
Lemma fst_pick_rec_tl: forall A:Type, forall n:nat, forall Lhd Ltl : list A, 
   (n <= length Lhd) -> fst(pick_rec A n Lhd) = fst (pick_rec A n (Lhd ++ Ltl)).
intro A.
induction n.
intro Lhd.
simpl.
destruct Lhd, Ltl.
auto.
auto.
auto.
auto.
simpl.
destruct Lhd.
simpl.
intros Ltl H.
apply NPeano.Nat.nle_succ_0 in H.
contradiction.
simpl.
intro Ltl.
intro H.
apply le_S_n in H.
f_equal.
apply IHn.
exact H.
Qed.

Lemma fst_pick_rec_app: forall A:Type, forall n:nat, forall L1 L2: list A,
(length L1) = n -> fst(pick_rec A n (L1++L2)) = L1.
intros A n L1 L2 Hlen.
rewrite<- fst_pick_rec_tl.
rewrite fst_pick_rec.
reflexivity.
exact Hlen.
rewrite Hlen.
apply le_n.
Qed.

Lemma snd_pick_rec: 
  forall A:Type, forall L1 L2 : list A, forall n:nat,
    (length L1) = n -> (snd (pick_rec A n (L1 ++ L2))) = L2.
intros A L1.
induction L1.
intros L2 n Hlen.
simpl in Hlen.
rewrite <- Hlen.
simpl.
destruct L2.
simpl; reflexivity.
simpl; reflexivity.
intros L2 n Hlen.
simpl in Hlen.
rewrite <- Hlen.
simpl.
apply IHL1.
reflexivity.
Qed.

Lemma snd_pick_rec_tl: forall A:Type, forall n:nat, forall Lhd Ltl : list A, 
   (n <= length Lhd) -> snd(pick_rec A n Lhd)++Ltl = snd (pick_rec A n (Lhd ++ Ltl)).
intros A n.
induction n.
destruct Lhd.
simpl.
destruct Ltl.
auto.
auto.
simpl.
reflexivity.
intros Lhd Ltl H.
destruct Lhd.
simpl.
destruct Ltl.
auto.
simpl.
simpl in H.
apply NPeano.Nat.nle_succ_0 in H.
contradiction.
simpl.
apply IHn.
simpl in H.
apply le_S_n in H.
exact H.
Qed.

Lemma snd_pick_rec_length:  forall A:Type, forall n:nat, forall L: list A, 
   (length (snd (pick_rec A n L))) = (length L) - n.
intros A n.
induction n.
simpl.
destruct L.
auto.
simpl.
auto.
simpl.
destruct L.
auto.
simpl.
apply IHn.
Qed.

Lemma weigh_tl: forall n:nat, forall Lhd Ltl: coins, (n+n <= length Lhd) -> weigh n Lhd = weigh n (Lhd ++ Ltl).
induction n.
simpl.
unfold weigh.
simpl.
destruct Lhd.
simpl.
destruct Ltl.
auto.
auto.
auto.
intros Lhd Ltl Hlen.
unfold weigh.
rewrite (surjective_pairing (pick_rec coin (S n) Lhd) ).
rewrite (surjective_pairing (pick_rec coin (S n) (Lhd++Ltl))).
rewrite (surjective_pairing _).
rewrite (surjective_pairing (pick_rec coin (S n) (snd (pick_rec coin (S n) (Lhd ++ Ltl))))).
rewrite <- fst_pick_rec_tl.
rewrite <- snd_pick_rec_tl.
rewrite <- fst_pick_rec_tl.
reflexivity.
simpl.
destruct Lhd.
simpl.
simpl in Hlen.
apply NPeano.Nat.nle_succ_0 in Hlen.
contradiction.
simpl.
rewrite snd_pick_rec_length.
apply  NPeano.Nat.le_add_le_sub_r.
simpl in Hlen.
apply le_S_n in Hlen.
replace (S n + n) with (n + S n).
exact Hlen.
rewrite plus_comm at 1.
reflexivity.
apply (NPeano.Nat.le_le_add_le 0 (S n)).
apply le_0_n.
rewrite <- plus_n_O.
exact Hlen.
apply (NPeano.Nat.le_le_add_le 0 (S n)).
apply le_0_n.
rewrite <- plus_n_O.
exact Hlen.
Qed.  

Lemma swap_length: forall A:Type, forall L: list A, forall n m:nat,
    length L = length (swap A L n m).
intros A L.
induction L.
simpl; reflexivity.
simpl.
unfold swap.
simpl.
induction n.
induction m.
simpl; reflexivity.
simpl.
apply eq_S.
apply IHL.
simpl.
intro m.
rewrite app_length.
unfold length at 3.
rewrite NPeano.Nat.add_succ_r.
f_equal.
rewrite<- app_length.
apply IHL.
Qed.

Lemma procDepth_tl : forall p:proc, forall Lhd Ltl : coins,   
      ((procDepth p) <= (length Lhd)) -> (procEval p (Lhd++Ltl)) = (procEval p Lhd) ++ Ltl.
intro p.
induction p.
simpl; reflexivity.
intros Lhd Ltl.
unfold procDepth.
fold procDepth.
intro Hlen.
unfold procEval.
fold procEval.
rewrite swap_tl.
apply IHp.
apply Max.max_lub_r in Hlen.
rewrite <- swap_length.
exact Hlen.
apply Max.max_lub_l in Hlen.
exact Hlen.
unfold procDepth.
fold procDepth.
intros Lhd Ltl Hlen.
unfold procEval.
fold procEval.
rewrite IHp1.
rewrite IHp2.
rewrite IHp3.
rewrite<- weigh_tl.
destruct (weigh n Lhd).
reflexivity.
reflexivity.
reflexivity.
apply Max.max_lub_l in Hlen.
exact Hlen.
apply Max.max_lub_r in Hlen.
apply Max.max_lub_r in Hlen.
exact Hlen.
apply Max.max_lub_r in Hlen.
apply Max.max_lub_l in Hlen.
apply Max.max_lub_r in Hlen.
exact Hlen.
apply Max.max_lub_r in Hlen.
apply Max.max_lub_l in Hlen.
apply Max.max_lub_l in Hlen.
exact Hlen.
Qed.

Lemma p4Works: forall L: coins, (length L = 4) -> (exactlyn 1 L) -> ((hd gold (procEval p4 L)) = fake).
intro L.
intro Hlen.
intro Hone.
assert (length (procEval p4 L) = length L).
apply Permutation_length.
symmetry.
apply procEval_permutes.
rewrite Hlen in H.
induction L.
inversion Hone.
induction L.
inversion Hlen.
induction L; inversion Hlen.
induction L; inversion Hlen.
induction L.
unfold procEval; unfold p4.
unfold weigh.
unfold pick_rec.
simpl.
unfold coin_sum.
simpl.
clear IHL.
clear IHL0.
clear IHL1.
clear IHL2.
clear H1.
clear H2.
clear Hlen.
inversion Hone.
inversion H2.
simpl; reflexivity.
inversion H2.
simpl; reflexivity.
simpl.
inversion H6.
inversion H10.
simpl; reflexivity.
inversion H10.
simpl; reflexivity.
simpl.
rewrite H12.
rewrite <- H12 in H10.
inversion H10.
inversion H14.
clear IHL.
clear IHL0.
clear IHL1.
clear IHL2.
clear H1.
clear H2.
clear IHL3.
simpl in Hlen.
exfalso.
apply eq_add_S in Hlen.
apply eq_add_S in Hlen.
apply eq_add_S in Hlen.
apply eq_add_S in Hlen.
apply NPeano.Nat.neq_succ_0 in Hlen.
exact Hlen.
Qed.

Lemma p12Depth: procDepth p12 = 12.
auto.
Qed.

Lemma list_length0 : forall A:Type, forall L: list A, (length L) = 0 -> L= [].
intros A L.
induction L.
simpl.
trivial.
simpl.
intro.
discriminate.
Qed.

Lemma breakup: forall n m k, n = (m+k) -> forall A:Type, forall Ln : list A, 
    length(Ln) = n -> exists Lm Lk : list A, (Ln = Lm ++ Lk) /\ (length Lm = m) /\ (length Lk = k).
intro n.
induction n.
intros m k Hmk A Ln.
exists [].
exists [].
simpl.
apply conj.
apply list_length0; exact H.
symmetry in Hmk.
apply plus_is_O in Hmk.
apply conj.
symmetry.
apply Hmk.
symmetry.
apply Hmk.
intros m k Hmk A Ln.
destruct Ln.
simpl.
intro.
symmetry in H.
apply NPeano.Nat.neq_succ_0 in H.
contradiction.
simpl.
intro H.
apply NPeano.Nat.succ_inj in H.
destruct m.
destruct k.
apply NPeano.Nat.neq_succ_0 in Hmk.
contradiction.
simpl in Hmk.
apply NPeano.Nat.succ_inj in Hmk.
elim (IHn 0 k Hmk A Ln H).
intro Lm.
intro.
elim H0.
intro Lk.
intro.
exists Lm.
exists (a::Lk).
elim H1.
intro H2.
intro H3; elim H3; intro H4; intro H5.
apply list_length0 in H4.
rewrite H4.
simpl.
apply conj.
f_equal.
rewrite H4 in H2.
simpl in H2.
exact H2.
apply conj.
reflexivity.
f_equal.
exact H5.
rewrite plus_Sn_m in Hmk. 
apply NPeano.Nat.succ_inj in Hmk.
elim (IHn m k Hmk A Ln H).
intro Lm.
intro H0; elim H0; intro Lk.
intro H1.
elim H1; intro H2; intro H3; elim H3; intro H4; intro H5.
exists (a::Lm); exists Lk.
rewrite<- app_comm_cons.
apply conj.
f_equal.
exact H2.
simpl.
apply conj.
apply eq_S.
exact H4.
exact H5.
Qed.

Lemma exactlyn_len: forall L:coins,  forall n:nat, exactlyn n L -> n <= (length L).
intro L.
induction L.
intro n.
inversion 1.
simpl.
apply le_refl.
intro n.
inversion 1.
simpl.
apply le_n_S.
apply IHL.
exact H2.
simpl.
apply le_S.
apply IHL.
exact H2.
Qed.

Lemma exactlyn_nil: forall n:nat, exactlyn n [] -> n = 0.
intro n.
inversion 1.
reflexivity.
Qed.

Lemma exactlyn_gold_rev: forall L:coins, forall n:nat, exactlyn n (gold::L) -> exactlyn n L.
intro.
induction L.
intro n.
inversion 1.
exact H2.
intro n.
inversion 1.
exact H2.
Qed.

Lemma exactlyn_fake_rev: forall L:coins, forall n:nat, exactlyn n (fake::L) -> exactlyn (pred n) L.
intros L n.
inversion 1.
simpl.
exact H2.
Qed.
 
Lemma exactlyn_app: 
  forall L1 :coins, forall n1:nat, 
    exactlyn n1 L1 -> 
    forall L2 : coins, forall n2:nat, 
      exactlyn n2 L2 -> exactlyn (n1 + n2) (L1 ++ L2).
intros L1 n1.
induction 1.
simpl.
tauto.
simpl.
intros L2 n2 Hn2.
apply exactlyn_fake.
apply IHexactlyn.
exact Hn2.
intros L2 n2 Hn2.
simpl.
apply exactlyn_gold.
apply IHexactlyn.
exact Hn2.
Qed.

Lemma exacltyn_app_comm: forall L1 L2 : coins, forall n:nat, exactlyn n (L1 ++ L2) -> exactlyn n (L2 ++ L1).
intros L1 L2 n.
apply exactlyn_permutes.
apply Permutation_app_comm.
Qed.

Lemma exactlyn_app_rev: forall n:nat, forall L : coins, 
  exactlyn n L -> forall L1 L2 : coins, L = L1 ++ L2 ->
      exists n1 n2:nat, (exactlyn n1 L1 /\ exactlyn n2 L2 /\ n = (n1 + n2)).
intros n L.
intro H.
induction H.
intros L1 L2.
intro Hnil.
exists 0.
exists 0.
simpl.
symmetry in Hnil.
apply app_eq_nil in Hnil.
decompose [and] Hnil.
rewrite H; rewrite H0.
apply conj.
constructor.
apply conj.
constructor.
reflexivity.
intros L1 L2.
destruct L1.
simpl.
intro HL2.
rewrite<- HL2.
exists 0.
exists (S n).
apply conj.
constructor.
apply conj.
apply exactlyn_fake.
exact H.
simpl.
reflexivity.
rewrite <- app_comm_cons.
intro H1.
assert (ns = L1 ++ L2).
change ns with (tl (fake::ns)).
rewrite H1.
simpl; reflexivity.
specialize (IHexactlyn L1 L2 H0).
elim IHexactlyn.
intro n1.
intro Htemp.
elim Htemp.
intro n2.
intro Hand.
decompose [and] Hand.
exists (S n1).
exists n2.
apply conj.
replace c with fake.
apply exactlyn_fake.
exact H2.
change c with (hd fake (c :: L1 ++ L2)).
rewrite <- H1.
simpl; reflexivity.
apply conj.
exact H4.
simpl.
f_equal.
exact H5.
intros L1 L2 Happ.
destruct L1.
simpl in Happ.
exists 0.
exists n.
apply conj.
constructor.
apply conj.
rewrite <- Happ.
apply exactlyn_gold.
exact H.
simpl; reflexivity.
assert (ns = L1 ++ L2).
change ns with (tl (gold::ns)).
rewrite Happ.
simpl.
reflexivity.
specialize (IHexactlyn L1 L2 H0).
elim IHexactlyn.
intro n1.
intro Htemp.
elim Htemp.
intro n2.
intro Hand.
decompose [and] Hand.
exists n1; exists n2.
apply conj.
replace c with gold.
apply exactlyn_gold.
exact H1.
rewrite<- app_comm_cons in Happ.
change c with (hd gold (c :: L1 ++ L2)).
rewrite <- Happ.
simpl; reflexivity.
apply conj.
exact H3.
exact H4.
Qed.

Lemma length_0: forall A:Type, forall L:list A, length L = 0 -> L = [].
intros A L.
induction L.
simpl; tauto.
simpl.
intro H.
apply NPeano.Nat.neq_succ_0 in H.
contradiction.
Qed.

Lemma nat_compare_plus: forall a n m:nat, nat_compare (a+n) (a+m) = nat_compare n m.
intro a.
induction a.
simpl; tauto.
intros n m.
replace (S a + n) with (S (a+n)).
replace (S a + m) with (S (a+m)).
rewrite nat_compare_S.
apply IHa.
auto.
auto.
Qed.

Definition flip x :=
  match x with
    | Gt => Lt
    | Lt => Gt
    | Eq => Eq
end.
              
            
Lemma nat_compare_flip: forall n m:nat, nat_compare n m = flip (nat_compare m n).
intro n.
induction n.
intro m.
induction m.
simpl.
reflexivity.
simpl.
reflexivity.
induction m.
simpl.
reflexivity.
simpl.
apply IHn.
Qed.  

Lemma nat_compare_0_minus: 
  forall m n : nat, n <= m -> nat_compare 0 (m - n) = nat_compare n m.
intros m n Hle.
apply le_lt_or_eq in Hle.
decompose [or] Hle.
assert (Hlt := H).
apply nat_compare_lt in Hlt.
rewrite Hlt.
assert (Hlt2 := H).
apply lt_le_S in H.
apply (minus_le_compat_r (S n) m (S n)) in H. 
rewrite minus_diag in H.
rewrite NPeano.Nat.sub_succ_r in H. 
apply NPeano.Nat.le_pred_le in H.
assert (0 < m - n). 
apply (plus_lt_reg_l 0 (m - n) n). 
rewrite <- le_plus_minus.
rewrite <- plus_n_O.
exact Hlt2.
apply lt_le_weak.
exact Hlt2.
apply nat_compare_lt in H0.
rewrite H0.
reflexivity.
assert (Heq := H).
apply (nat_compare_eq_iff n m) in H.
rewrite H.
rewrite Heq.
rewrite minus_diag.
simpl.
reflexivity.
Qed.

Lemma nat_compare_minus_0:
  forall m n:nat, n<=m -> nat_compare (m - n) 0 = nat_compare m n.
intros m n.
rewrite nat_compare_flip.
rewrite (nat_compare_flip m n).
intro Hlen.
apply f_equal.
apply nat_compare_0_minus.
exact Hlen.
Qed.


Lemma nat_compare_minus: forall a n m:nat, a>=n -> a>=m -> nat_compare (a-n) (a-m) = nat_compare m n.
intro a.
induction a.
intros n m Hn Hm.
apply le_n_0_eq in Hn.
apply le_n_0_eq in Hm.
rewrite <- Hn.
rewrite <- Hm.
simpl.
reflexivity.
intros n m Hn Hm.
apply le_lt_or_eq in Hn.
apply le_lt_or_eq in Hm.
decompose [or] Hn.
decompose [or] Hm.
apply lt_n_Sm_le in H.
apply lt_n_Sm_le in H0.
rewrite <- (minus_Sn_m a n H).
rewrite <- (minus_Sn_m a m H0).
rewrite nat_compare_S.
apply IHa.
exact H.
exact H0.
rewrite H0.
rewrite minus_diag.
apply nat_compare_minus_0.
apply lt_le_weak.
exact H.

decompose [or] Hm.
rewrite H.
rewrite minus_diag.
apply nat_compare_0_minus.
apply lt_le_weak.
exact H0.
rewrite H.
rewrite H0.
rewrite minus_diag.
simpl.
assert (a=a).
reflexivity.
apply nat_compare_eq_iff in H1.
rewrite H1.
reflexivity.
Qed.

Lemma weigh_split: 
  forall n:nat, forall a:coin, forall L1 L2 :coins,
    length L1 = n -> length L2 = n  -> weigh (S n) (a::L1 ++ (a::L2)) = weigh n (L1 ++ L2).
intro n.
induction n.
intros a L1 L2 Hlen1 Hlen2.
apply length_0 in Hlen1.
apply length_0 in Hlen2.
rewrite Hlen1; rewrite Hlen2.
simpl.
unfold weigh.
unfold pick_rec.
simpl.
apply nat_compare_eq_iff.
reflexivity.
intros a L1 L2.
destruct L1.
intro Hlen1.
simpl in Hlen1.
symmetry in Hlen1.
apply NPeano.Nat.neq_succ_0 in Hlen1.
contradiction.
destruct L2.
intros Hlen1 Hlen2.
symmetry in Hlen2.
simpl in Hlen2.
apply NPeano.Nat.neq_succ_0 in Hlen2.
contradiction.
intro Hlen1; simpl in Hlen1.
intro Hlen2; simpl in Hlen2.
unfold weigh in IHn.
specialize (IHn a L1 L2).
rewrite (surjective_pairing (pick_rec coin (S n) (a :: L1 ++ a :: L2))) in IHn.
rewrite app_comm_cons in IHn.
rewrite snd_pick_rec in IHn.
rewrite fst_pick_rec_app in IHn.
rewrite (surjective_pairing (pick_rec coin (S n) _ )) in IHn.
rewrite fst_pick_rec in IHn.
apply eq_add_S in Hlen1.
apply eq_add_S in Hlen2.
specialize (IHn Hlen1 Hlen2).
rewrite (surjective_pairing (pick_rec coin n (L1 ++ L2))) in IHn.
rewrite fst_pick_rec_app in IHn.
rewrite (surjective_pairing (pick_rec coin n _)) in IHn.
rewrite snd_pick_rec in IHn.
rewrite fst_pick_rec in IHn.
unfold weigh.
rewrite (surjective_pairing (pick_rec coin (S (S n)) (a::(c :: L1) ++ a::c0::L2))).
rewrite app_comm_cons.
rewrite snd_pick_rec.
rewrite fst_pick_rec_app.
rewrite (surjective_pairing (pick_rec coin (S (S n)) _)).
rewrite fst_pick_rec.
rewrite (surjective_pairing (pick_rec coin (S n) _)).
rewrite snd_pick_rec.
rewrite fst_pick_rec_app.
rewrite (surjective_pairing (pick_rec _ (S n) _)).
rewrite fst_pick_rec.
rewrite sum_cons.
rewrite sum_cons.
rewrite sum_cons; rewrite sum_cons.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite <-  plus_assoc.
rewrite <- plus_assoc.
rewrite nat_compare_plus.
reflexivity.
simpl; auto.
simpl; auto.
simpl; auto.
simpl; auto.
simpl; auto.
simpl; auto.
auto.
simpl;auto.
simpl;auto.
simpl;auto.
simpl;auto.
simpl;auto.
Qed.

Lemma length_nil_S: forall A:Type, forall n:nat, length ([]:list A) = S n -> False.
intros A N H.
simpl in H.
symmetry in H.
apply NPeano.Nat.neq_succ_0 in H.
exact H.
Qed.

Lemma exactlyn_sum: 
  forall L:coins, forall n:nat,
    exactlyn n L -> (coin_sum L) = n + 2 * ((length L) - n).
intros L n Hex.
induction Hex.
simpl; reflexivity.
simpl.
unfold coin_sum.
simpl.
f_equal.
unfold coin_sum in IHHex.
simpl in IHHex.
exact IHHex.
simpl.
destruct n.
simpl.
rewrite<- plus_Snm_nSm.
rewrite plus_Sn_m.
unfold coin_sum.
simpl.
f_equal.
f_equal.
unfold coin_sum in IHHex.
simpl in IHHex.
simpl in IHHex.
replace (length ns - 0) with (length ns) in IHHex.
exact IHHex.
rewrite<- minus_n_O.
reflexivity.
unfold coin_sum.
simpl.
simpl in IHHex.
unfold coin_sum in IHHex.
rewrite IHHex.
simpl.
f_equal.
rewrite plus_n_Sm.
rewrite plus_n_Sm.
f_equal.
rewrite <- plus_Sn_m.
rewrite NPeano.Nat.sub_succ_r.
rewrite <-  (S_pred (length ns -  n) 0).
rewrite plus_n_Sm.
rewrite <- plus_Sn_m.
rewrite <- (S_pred (length ns - n) 0).
reflexivity.

apply exactlyn_len in Hex.
apply (minus_le_compat_r (S n) (length ns) n) in Hex.
rewrite <- minus_Sn_m in Hex.
rewrite NPeano.Nat.sub_diag in Hex.
apply le_lt_n_Sm in Hex.
apply lt_S_n in Hex.
exact Hex.
auto.

apply exactlyn_len in Hex.
apply (minus_le_compat_r (S n) (length ns) n) in Hex.
rewrite <- minus_Sn_m in Hex.
rewrite NPeano.Nat.sub_diag in Hex.
apply le_lt_n_Sm in Hex.
apply lt_S_n in Hex.
exact Hex.
auto.

Qed.

Lemma exactlyn_nat_compare: 
  forall L1 L2 : coins, forall n1 n2 : nat,
    (length L1 = length L2) ->
    exactlyn n1 L1 ->
    exactlyn n2 L2 ->
    nat_compare (coin_sum L1) (coin_sum L2) = nat_compare n2 n1.
intros L1 L2 n1 n2 Hlen Hex1 Hex2.
rewrite (exactlyn_sum L1 n1 Hex1).
rewrite (exactlyn_sum L2 n2 Hex2).
rewrite Hlen.
apply exactlyn_len in Hex1.
apply exactlyn_len in Hex2.
rewrite Hlen in Hex1.
simpl.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite plus_assoc.
rewrite <- plus_n_O.
rewrite <- plus_n_O.
rewrite <- (le_plus_minus n1 (length L2) Hex1).
rewrite <- (le_plus_minus n2 (length L2) Hex2).
rewrite nat_compare_plus.
rewrite (nat_compare_minus (length L2) n1 n2 Hex1 Hex2).
reflexivity.
Qed.

Lemma weigh_defn : 
  forall n:nat, forall L1 L2 : coins, 
    length L1 = n -> 
    length L2 = n ->
    forall n1 n2 : nat,
      exactlyn n1 L1 ->
      exactlyn n2 L2 ->
      weigh n (L1 ++ L2) = nat_compare n2 n1.
intros n L1 L2 Hlen1 Hlen2 n1 n2 Hex1 Hex2.
unfold weigh.
rewrite (surjective_pairing (pick_rec _ n _)).
rewrite (snd_pick_rec _ L1 _ _  Hlen1).
rewrite (surjective_pairing (pick_rec _ n _)).
rewrite (fst_pick_rec_app _ n _ _ Hlen1).
rewrite (surjective_pairing (pick_rec _ n L2)).
rewrite (fst_pick_rec _ L2 n Hlen2).
assert (length L1 = length L2).
rewrite Hlen1; rewrite Hlen2; reflexivity.
apply (exactlyn_nat_compare L1 L2 n1 n2 H Hex1 Hex2).
Qed.

Lemma weigh_eq: 
  forall L : coins,
    exactlyn 0 L -> forall n:nat, (n+n = length L) -> weigh n L = Eq.
intros L Hex n Hlen.
assert (Htriv:length L = length L).
reflexivity.
symmetry in Hlen.
elim (breakup (length L) n n Hlen coin L Htriv).
intros L1 H2.
elim H2.
intros L2 Hprops.
decompose [and] Hprops.
rewrite H.
elim (exactlyn_app_rev 0 L Hex L1 L2).
intros n1 Ht.
elim Ht.
intros n2 Hx.
decompose [and] Hx.
symmetry in H6.
clear Hx.
apply plus_is_O in H6.
decompose [and] H6.
rewrite H4 in H0.
rewrite H7 in H5.
rewrite (weigh_defn n L1 L2 H1 H3 0 0 H0 H5).
simpl.
reflexivity.
exact H.
Qed.

 
Lemma hd_app: forall A:Type, forall L1 L2: list A, forall a : A, 
    length L1 > 0 -> hd a (L1 ++ L2) = hd a L1.            
intros A L1 L2 a Hlen.
destruct L1.
simpl in Hlen.
apply gt_irrefl in Hlen.
contradiction.
simpl.
reflexivity.
Qed.


Lemma p12Works: forall ns :coins, (length ns = 12) -> (exactlyn 1 ns) -> ((hd gold (procEval p12 ns)) = fake).
intros ns Hlen.
unfold p12.
unfold procEval.
fold procEval.
assert (H12 : (12 = 8 + 4)).
auto.
elim (breakup 12 8 4 H12 coin ns Hlen).
intros L8.
intro H1; elim H1.
intro L4.
intro H2; elim H2.
intro Hcombine.
intro H3; elim H3.
intros H8len H4len.
intro Hns.
elim (exactlyn_app_rev 1 ns Hns L8 L4 Hcombine).
intro n1.
intro Hsimpl.
elim Hsimpl.
intro n2.
intro Hcc.
decompose [and] Hcc.
assert (H8: 8 = 4 + 4).
auto.
elim (breakup 8 4 4 H8 coin L8 H8len).
intro L41.
intro H1'; elim H1'.
intro L42.
intro Hcombine'.
decompose [and] Hcombine'.
rewrite Hcombine.
elim (exactlyn_app_rev n1 L8 H L41 L42 H0). 
intro n11.
intro Hex.
elim Hex.
intro n21.
intro Hex2.
decompose [and] Hex2.
clear H1 H2 Hsimpl H1' Hcombine' Hex H3 Hcc Hex2.
symmetry in H5.
apply NPeano.Nat.eq_add_1 in H5.
elim H5.
intro Hn1n2.
decompose [and] Hn1n2.
clear Hn1n2.
rewrite H2 in H4.
rewrite H1 in H.
rewrite H0.
assert (4 + 4 <= (length (L41 ++ L42))).
rewrite app_length.
rewrite H7; rewrite H9.
simpl.
apply le_refl.
rewrite<- (weigh_tl 4 (L41 ++ L42) L4 H3). 
rewrite (weigh_defn 4 L41 L42 H7 H9 n11 n21 H6 H11).
rewrite H1 in H13.
symmetry in H13.
apply NPeano.Nat.eq_add_1 in H13.
decompose [or] H13.
decompose [and] H10.
rewrite H14.
rewrite H15.
Arguments procEval : simpl nomatch.
simpl.
rewrite<- app_assoc.
rewrite procDepth_tl.
rewrite hd_app.
rewrite p4Works.
reflexivity.
exact H7.
rewrite H14 in H6.
exact H6.
rewrite<- procEval_length.
rewrite H7.
apply gt_Sn_O.
simpl.
rewrite H7.
apply le_refl.
(* Start of second case *)
decompose [and] H10.
rewrite H14; rewrite H15.
simpl.
rewrite (swap_tl coin (L41 ++ L42) L4 4 4 H3).
rewrite<- H7 at 1.
rewrite<- H9 at 1.
rewrite swap_app.
rewrite procDepth_tl.
rewrite hd_app.
rewrite procDepth_tl.
rewrite hd_app.
rewrite p4Works.
reflexivity.
exact H9.
rewrite H15 in H11.
exact H11.
rewrite<- procEval_length.
rewrite H9.
apply gt_Sn_O.
simpl.
rewrite H9.
apply le_refl.
rewrite<- procEval_length.
rewrite app_length.
rewrite H7; rewrite H9.
simpl.
apply gt_Sn_O.
simpl.
rewrite app_length.
rewrite H7; rewrite H9; simpl.
auto.
intro Hf.
decompose [and] Hf.
rewrite H2 in H4.
rewrite H1 in H.
rewrite<- weigh_tl. 
symmetry in H8len.
rewrite (weigh_eq L8 H 4 H8len).
rewrite H8len.
rewrite<- H4len.
rewrite (swap_app _ L8 L4).
rewrite procDepth_tl.
rewrite hd_app.
apply p4Works.
exact H4len.
exact H4.
rewrite <- procEval_length.
rewrite H4len.
apply gt_Sn_O.
simpl.
rewrite H4len.
apply le_refl.
rewrite H8len.
simpl.
apply le_refl.
Qed.


(** * Inversion.

  In this section we define an evaluator that runs proc backwards.
  The goal is to return every possible input that could produce the
  given set of outputs.  This will be useful for arguing about optimal
  solutions.

*)

Definition weighInv cmp n gs := 
  match (weigh n gs), cmp with
    | Lt, Lt => true
    | Gt, Gt => true
    | Eq, Eq => true
    | _, _ => false
  end.

Fixpoint procEvalInv (p:proc) (gs : list coins ) : list coins :=
  match p with
    | Stop => gs
    | Swap n m p => List.map (fun g => (swap _ g m n)) (procEvalInv p gs)
    | Weigh n pLt pEq pGt => 
      let gLt := procEvalInv pLt gs in
      let gEq := procEvalInv pEq gs in
      let gGt := procEvalInv pGt gs in
      ((List.filter (fun g => weighInv Lt n g) gLt) 
         ++ (List.filter (fun g => weighInv Eq n g) gEq) 
         ++ (List.filter (fun g => weighInv Gt n g) gGt))
  end.

Compute (procEvalInv p4 [[fake;gold;gold;gold]]).
Compute (swap _ (swap _ [fake;gold;gold;gold] 1 2) 2 1).

Lemma procEvalInv_compose:
  forall p : proc, forall L : list coins, forall gInv : coins,
    In gInv (procEvalInv p L) 
    -> (exists g : coins,  In g L /\ In gInv (procEvalInv p [g])).
induction p.
simpl.
intros L gInv Hin.
exists gInv.
apply conj.
exact Hin.
left; reflexivity.
simpl.
intros L gInv Hin.
apply in_map_iff in Hin.
elim Hin.
intro gx.
intro Hand.
decompose [and] Hand.
rewrite<- H.
elim (IHp L gx).
intros g Hand2.
decompose [and] Hand2.
exists g.
apply conj.
exact H1.
set (fm := (fun g0:coins => swap coin g0 n0 n)).
replace (swap coin gx n0 n) with (fm gx).
apply in_map.
exact H2.
unfold fm.
reflexivity.
exact H0.
simpl.
intros L gInv.
intro Hin.
apply in_app_or in Hin.
decompose [or] Hin.
rewrite filter_In in H.
decompose [and] H.
elim (IHp1 L gInv).
intros g H2.
exists g.
apply conj.
decompose [and] H2.
exact H3.
apply in_or_app.
left.
apply filter_In.
apply conj.
decompose [and] H2.
exact H4.
exact H1.
exact H0.
clear Hin.
apply in_app_or in H.
decompose [or] H.
clear H.
rewrite filter_In in H0.
decompose [and] H0.
elim (IHp2 L gInv).
intros g H2.
exists g.
apply conj.
decompose [and] H2.
exact H3.
apply in_or_app; right; apply in_or_app.
left.
apply filter_In.
apply conj.
decompose [and] H2.
exact H4.
exact H1.
exact H.
clear H.
rewrite filter_In in H0.
decompose [and] H0.
elim (IHp3 L gInv).
intros g H2.
exists g.
apply conj.
decompose [and] H2.
exact H3.
apply in_or_app; right; apply in_or_app; right.
apply filter_In.
apply conj.
decompose [and] H2.
exact H4.
exact H1.
exact H.
Qed.

(* Use swap_app and breakup for case where length is equal to m+n.
   Use swap_tl for case where longer.
   Is not true if shorter but we don't care. *)
Lemma swapInv_len_eq: 
  forall A : Type, forall L : list A, forall n m : nat,
    (length L = (n+m)) -> swap A (swap A L n m) m n = L.
intros A L n m Hlen.
elim (breakup (length L) n m Hlen A L).
intros Ln HLm.
elim HLm.
intros Lm Hnm.
decompose [and] Hnm.
rewrite H.
rewrite<- H1.
rewrite<- H2.
rewrite swap_app.
rewrite swap_app.
f_equal.
reflexivity.
Qed.

Lemma swapInv_len_geq: 
  forall A : Type, forall L : list A, forall n m : nat,
    (length L >= (n+m)) -> swap A (swap A L n m) m n = L.
intros A L n m Hlen.
elim (NPeano.Nat.le_exists_sub (n+m)(length L)).
intros p Hp.
decompose [and] Hp.
rewrite plus_comm in H.
elim (breakup (length L) (n + m) p H A L).
intros Lmn HLmn.
elim HLmn.
intros Lp HLp.
decompose [and] HLp.
rewrite H1.
rewrite swap_tl.
rewrite swap_tl.
f_equal.
apply swapInv_len_eq.
exact H3.
rewrite<- swap_length.
rewrite plus_comm.
erewrite H3.
reflexivity.
rewrite H3.
reflexivity.
reflexivity.
exact Hlen.
Qed.


(* First we show that procEvalInv contains all possible inputs.  We
call this property being full. *)
Lemma procEvalInv_is_full : 
  forall p:proc,forall g:coins, 
    (procDepth p <= length g) -> 
    (List.In g (procEvalInv p [procEval p g]))
.
intro p.
induction p.
simpl.
intros g Hlen.
left.
reflexivity.
intros g Hlen.
unfold procEvalInv.
unfold procEval.
simpl.
fold procEval.
fold procEvalInv.
apply in_map_iff.
exists (swap coin g n n0).
rewrite swapInv_len_geq.
apply conj.
reflexivity.
apply IHp.
rewrite<- swap_length.
unfold procDepth in Hlen.
simpl in Hlen.
fold procDepth in Hlen.
apply Max.max_lub_r in Hlen.
exact Hlen.
unfold procDepth in Hlen.
fold procDepth in Hlen.
apply Max.max_lub_l in Hlen.
exact Hlen.
intros g Hlen.
unfold procEval.
fold procEval.
unfold procEvalInv.
fold procEvalInv.
remember (weigh n g) as wg.
destruct wg.
apply in_or_app.
right.
apply in_or_app.
left.
apply filter_In.
apply conj.
apply IHp2.
unfold procDepth in Hlen.
fold procDepth in Hlen.
apply Max.max_lub_r in Hlen.
apply Max.max_lub_l in Hlen.
apply Max.max_lub_r in Hlen.
exact Hlen.
unfold weighInv.
rewrite<- Heqwg.
reflexivity.
apply in_or_app.
left.
apply filter_In.
apply conj.
apply IHp1.
unfold procDepth in Hlen.
fold procDepth in Hlen.
apply Max.max_lub_r in Hlen.
apply Max.max_lub_l in Hlen.
apply Max.max_lub_l in Hlen.
exact Hlen.
unfold weighInv.
rewrite<- Heqwg. 
reflexivity.
apply in_or_app.
right.
apply in_or_app.
right.
apply filter_In.
apply conj.
apply IHp3.
unfold procDepth in Hlen.
fold procDepth in Hlen.
apply Max.max_lub_r in Hlen.
apply Max.max_lub_r in Hlen.
exact Hlen.
unfold weighInv.
rewrite<- Heqwg.
reflexivity.
Qed.

Lemma procEvalInv_length:
  forall p:proc, forall g gInv :coins,
    In gInv (procEvalInv p [g]) -> (length gInv = length g).
intros p g.
induction p.
simpl.
intros gInv Hin.
decompose [or] Hin.
rewrite<- H.
reflexivity.
contradiction.
simpl.
intros gInv Hin.
apply in_map_iff in Hin.
elim Hin.
intro g2.
intro Hand.
decompose [and] Hand.
rewrite<- H.
rewrite<- swap_length.
apply IHp.
exact H0.
intros gInv Hin.
simpl in Hin.
apply in_app_or in Hin.
decompose [or] Hin.
apply IHp1.
apply filter_In in H.
decompose [and] H.
exact H0.
apply in_app_or in H.
decompose [or] H.
apply filter_In in H0.
decompose [and] H0.
apply IHp2.
exact H1.
apply filter_In in H0.
apply IHp3.
decompose [and] H0.
exact H1.
Qed.

Lemma max_lub_4: forall a b c d m : nat,
            max a (max (max b c) d) <= m -> a <= m /\ b <= m /\ c <= m /\ d <= m.
intros a b c d m H.
apply conj.
apply Max.max_lub_l in H.
exact H.
apply conj.
apply Max.max_lub_r in H.
apply Max.max_lub_l in H.
apply Max.max_lub_l in H.
exact H.
apply conj.
apply Max.max_lub_r in H.
apply Max.max_lub_l in H.
apply Max.max_lub_r in H.
exact H.
apply Max.max_lub_r in H.
apply Max.max_lub_r in H.
exact H.
Qed.

Lemma in_filter_app3: 
  forall A:Type, forall f1 f2 f3: A -> bool, forall L1 L2 L3: list A, forall a:A,
    In a ((filter f1 L1) ++ (filter f2 L2) ++ (filter f3 L3)) <->
        (In a L1 /\ (f1 a = true)) \/ 
        (In a L2 /\ (f2 a = true)) \/ 
        (In a L3 /\ (f3 a = true)).
intros A f1 f2 f3 L1 L2 L3 a.
apply conj.
intro H.
apply in_app_or in H.
decompose [or] H.
apply filter_In in H0.
auto.
apply in_app_or in H0.
decompose [or] H0.
apply filter_In in H1.
auto.
apply filter_In in H1.
auto.
intro H.
apply in_or_app.
elim H.
intro H1.
left.
apply filter_In.
exact H1.
intro H2or3.
elim H2or3.
intro H2.
right.
apply in_or_app.
left.
apply filter_In.
exact H2.
intro H3.
right.
apply in_or_app.
right.
apply filter_In.
exact H3.
Qed.

(* Now we directly show that procEvalInv is an inverse.  *)
Lemma procEvalInv_is_inverse : 
  forall p:proc, forall g gInv:coins,
    (procDepth p <= length g) ->
    In gInv (procEvalInv p [g]) -> 
    procEval p gInv = g.
intro p.
induction p.
simpl.
intros g gInv Hlen.
intro H.
decompose [or] H.
symmetry.
exact H0.
contradiction.
simpl.
intros g gInv Hlen.
intros HinGinv.
apply IHp.
apply Max.max_lub_r in Hlen.
exact Hlen.
apply in_map_iff in HinGinv.
elim HinGinv.
intro g2.
intro Hand.
decompose [and] Hand.
rewrite<- H.
rewrite swapInv_len_geq.
exact H0.
apply Max.max_lub_l in Hlen.
apply procEvalInv_length in H0.
rewrite H0.
rewrite plus_comm.
exact Hlen.
simpl.
intros g gInv Hlen.
intro Hin.
unfold procEval.
fold procEval.
apply in_filter_app3 in Hin.
unfold weighInv in Hin.
remember (weigh n gInv) as wngInv.
destruct wngInv.
apply IHp2.
apply max_lub_4 in Hlen.
decompose [and] Hlen.
exact H0.
decompose [and or] Hin.
discriminate H1.
exact H.
discriminate H1.
apply IHp1.
apply max_lub_4 in Hlen.
decompose [and] Hlen.
exact H1.
decompose [and or] Hin.
exact H0.
discriminate H1.
discriminate H1.
apply IHp3.
apply max_lub_4 in Hlen.
decompose [and] Hlen.
exact H3.
decompose [and or] Hin.
discriminate H1.
discriminate H1.
exact H.
Qed.

Theorem procEvalInv_is_full_inveerse:
  forall p:proc, forall g gInv:coins,
    (procDepth p <= length g) -> 
    ((In gInv (procEvalInv p [g])) <-> (procEval p gInv = g)).
intros p g gInv Hlen.
apply conj.
apply procEvalInv_is_inverse.
exact Hlen.
intro Heval.
rewrite<- Heval.
apply procEvalInv_is_full.
assert (Hleninv: length gInv = length g).
rewrite (procEval_length p gInv).
rewrite Heval.
reflexivity.
rewrite Hleninv.
exact Hlen.
Qed.

Lemma filter_length: 
  forall A:Type, forall f: A -> bool, forall L : list A,
    length (filter f L) <= length L.
intros A f L.
induction L.
simpl.
reflexivity.
unfold filter.
fold filter.
destruct (f a).
simpl.
apply le_n_S.
exact IHL.
simpl.
apply le_S.
exact IHL.
Qed.

(* We have established that procEvalInv is a real inverse function.
Now it remains to show that the output of procEvalInv has no
duplicates, and to bound the number of elements in the output of
procEvalInv. *)

Lemma pow_max: 
  forall a n m:nat, 
    a<>0 ->
    a ^ (max n m) = (max (a ^ n) (a ^ m)).
intros a n m Ha.
rewrite Nat.max_mono.
reflexivity.
unfold Morphisms.Proper.
unfold Morphisms.respectful.
intros x y.
intro H.
rewrite H.
reflexivity.
unfold Morphisms.Proper; unfold Morphisms.respectful.
intros x y Hle.
apply Nat.pow_le_mono_r.
exact Ha.
exact Hle.
Qed.

(* This lemma shows that the inverse function produces less than 3*(#
of uses of the scalw).  For a procedure to work, it must produce every possible input from the one correct output. *)

Lemma procEvalInv_length_bound: 
  forall p:proc, forall g:coins,
    length (procEvalInv p [g]) <= 3 ^ (procCost p).
intro p.
induction p.
intro g.
simpl.
trivial.
simpl.
intro g.
rewrite map_length.
apply IHp.
simpl.
intro g.
rewrite app_length.
rewrite app_length.
rewrite pow_max.
rewrite pow_max.
apply plus_le_compat.
apply (le_trans _ (length (procEvalInv p1 [g])) _ ).
apply filter_length.
apply Nat.max_le_iff.
left.
exact (IHp1 g).
apply plus_le_compat.
apply (le_trans _ (length (procEvalInv p2 [g])) _).
apply filter_length.
apply Nat.max_le_iff.
right.
apply Nat.max_le_iff.
left.
exact (IHp2 g).
apply (le_trans _ (length (procEvalInv p3 [g])) _ ).
apply filter_length.
rewrite<- plus_n_O.
apply Nat.max_le_iff; right.
apply Nat.max_le_iff; right.
exact (IHp3 g).
apply Nat.neq_succ_0.
apply Nat.neq_succ_0.
Qed.

(* We would like to show that the output is a set of values.
Eventually we want to use a cardinality argument to place a bound on
the number of weighings that are needed.  If we prove there are no
duplicates then our bound will be better.  *)

Lemma swap_unique: 
  forall A:Type, forall L1 L2 : list A, forall n m : nat,
    (n+m) <= (min (length L1) (length L2)) 
    -> (swap A L1 n m) = (swap A L2 n m)
    -> L1 = L2.
intros A L1 L2 n m Hlen Heq.
apply Nat.min_glb_iff in Hlen.
decompose [and] Hlen.
rewrite<- (swapInv_len_geq A L1 n m H).
rewrite<- (swapInv_len_geq A L2 n m H0).
f_equal.
exact Heq.
Qed.

(* Prove a basic prooperty of NoDup and map. *)
Lemma NoDup_map: 
  forall A B:Type, forall f:A -> B, forall L:list A,
    (forall a1 a2 : A, In a1 L -> In a2 L -> (f a1) = (f a2) -> a1 = a2)
    -> NoDup L -> NoDup (map f L).
intros A B.
induction L.
intros H1 H2; simpl; apply NoDup_nil.
intros Hf.
inversion 1.
simpl.
apply NoDup_cons.
intro Hc.
apply in_map_iff in Hc.
elim Hc.
intros a1.
intro Ht.
decompose [and] Ht.
apply Hf in H4.
rewrite H4 in H5.
generalize H5.
exact H2.
apply in_cons.
exact H5.
apply in_eq.
apply IHL.
intros a1 a2 Ha1 Ha2.
apply Hf.
apply in_cons.
exact Ha1.
apply in_cons.
exact Ha2.
exact H3.
Qed.

Lemma NoDup_app:
  forall A:Type, forall L1 L2 : list A,
    NoDup L1 
    -> NoDup L2
    -> ~(exists x:A, In x L1 /\ In x L2) -> NoDup (L1 ++ L2).
intro A.
induction L1.
intros L2 HL1 HL2 Hi.
simpl; exact HL2.
intros L2 HL1 HL2 Hi.
rewrite<- app_comm_cons.
apply NoDup_cons.
intro H.
apply in_app_iff in H.
decompose [or] H.
inversion HL1.
elim H3.
exact H0.
elim Hi.
exists a.
apply conj.
apply in_eq.
exact H0.
apply IHL1.
inversion HL1.
exact H2.
exact HL2.
intro Hi2.
elim Hi.
elim Hi2.
intros x Hx.
exists x.
decompose [and] Hx.
apply conj.
apply in_cons.
exact H.
exact H0.
Qed.
             

Lemma NoDup_filter:
  forall A : Type, forall f : A -> bool, forall L : list A,
    NoDup L -> NoDup (filter f L).
intros A f L.
induction 1.
simpl.
apply NoDup_nil.
simpl.
destruct (f x).
apply NoDup_cons.
intro Hx.
apply filter_In in Hx.
decompose [and] Hx.
elim H.
exact H1.
exact IHNoDup.
exact IHNoDup.
Qed.

Lemma NoDup_filter_app: 
forall A : Type,  forall f : A -> bool, forall L1 L2 : list A,
  NoDup L1 
  -> NoDup L2 
  -> (filter f L2 = nil) 
  -> NoDup ((filter f L1) ++ L2).
intros A f L1 L2 HL1 HL2 Hf.
apply NoDup_app.
apply NoDup_filter.
exact HL1.
exact HL2.
intro H.
elim H.
intros x Hand.
decompose [and] Hand.
apply filter_In in H0.
decompose [and] H0.
assert (Hb: In x (filter f L2)).
apply filter_In.
apply conj.
exact H1.
exact H3.
rewrite Hf in Hb.
apply (in_nil Hb).
Qed.
  

Lemma filter_app:
  forall A:Type, forall f : A -> bool, forall L1 L2: list A,
    (filter f (L1 ++ L2)) = (filter f L1) ++ (filter f L2).
intros A f L1.
induction L1.
simpl.
trivial.
simpl.
intro L2.
rewrite IHL1.
destruct (f a).
reflexivity.
reflexivity.
Qed.

Lemma filter_filter: 
  forall A:Type, forall f1 f2: A -> bool, forall L: list A, 
    (filter f1 (filter f2 L)) = (filter (fun x => (f1 x) && (f2 x)) L).
intros A f1 f2 L.
induction L.
simpl.
reflexivity.
simpl.
destruct (f2 a).
simpl.
replace (f1 a && true) with (f1 a).
rewrite IHL.
reflexivity.
rewrite andb_true_r.
reflexivity.
rewrite andb_false_r.
rewrite IHL.
reflexivity.
Qed.

Lemma filter_filter_empty:
  forall A:Type, forall f1 f2: A -> bool,
    (forall x:A, ((f1 x)=true -> (f2 x)=false) /\ ((f2 x)=true -> (f1 x)=false)) -> 
    forall L:list A, 
      (filter f1 (filter f2 L)) = [].
intros A f1 f2 H L.
rewrite filter_filter.
induction L.
simpl; reflexivity.
simpl.
remember (f2 a) as b.
destruct b.
generalize (H a).
intro Hne.
rewrite<- Heqb in Hne.
decompose [and] Hne.
rewrite H1.
simpl.
exact IHL.
reflexivity.
generalize (H a).
intro Hne.
rewrite<- Heqb in Hne.
rewrite andb_false_r.
exact IHL.
Qed.

Lemma app_eq_nil_rev: 
  forall A:Type, forall L1 L2 : list A,
    L1 = [] -> L2 = [] -> (L1 ++ L2 = []).
intros A L1 L2 H1 H2.
rewrite H1.
rewrite H2.
simpl.
reflexivity.
Qed.

Lemma procEvalInv_NoDup: 
  forall p : proc, forall L : list coins,
    (forall x:coins, In x L -> (procDepth p <= (length x)))
    -> NoDup L 
    -> NoDup (procEvalInv p L).
induction p.
simpl.
tauto.
simpl.
intros L Hp Hnodup.
apply NoDup_map.
intros a1 a2 Ha1 Ha2.
apply (swap_unique coin a1 a2 n0 n).
apply Min.min_glb.
apply procEvalInv_compose in Ha1.
elim Ha1.
intro g.
intros H.
decompose [and] H.
rewrite (procEvalInv_length p g a1 H1).
rewrite plus_comm.
apply (Max.max_lub_l _ (procDepth p) _).
apply Hp.
exact H0.
apply procEvalInv_compose in Ha2.
elim Ha2.
intros g H.
decompose [and] H.
rewrite (procEvalInv_length p g a2 H1).
rewrite plus_comm.
apply (Max.max_lub_l _ (procDepth p) _).
apply Hp.
exact H0.
apply IHp.
intros x Hin.
apply (Max.max_lub_r (n + n0) _ _).
apply Hp.
exact Hin.
exact Hnodup.
(* Case for weigh *)
simpl.
intros L Hp Hnodup.
apply NoDup_filter_app.
apply IHp1.
intros x Hin.
generalize (Hp x Hin).
apply le_trans.
apply Nat.max_le_iff.
right.
apply Nat.max_le_iff.
left.
apply Nat.max_le_iff.
left.
reflexivity.
exact Hnodup.
apply NoDup_filter_app.
apply IHp2.
intros x Hin.
generalize (Hp x Hin).
apply le_trans.
apply Nat.max_le_iff; right.
apply Nat.max_le_iff; left.
apply Nat.max_le_iff; right.
reflexivity.
exact Hnodup.
apply NoDup_filter.
apply IHp3.
intros x Hin.
generalize (Hp x Hin).
apply le_trans.
apply Nat.max_le_iff; right.
apply Nat.max_le_iff; right.
reflexivity.
exact Hnodup.
apply filter_filter_empty.
intro x.
unfold weighInv.
destruct (weigh n x).
auto.
auto.
auto.
rewrite filter_app.
apply app_eq_nil_rev.
apply filter_filter_empty.
intros x.
unfold weighInv.
destruct (weigh n x).
auto.
auto.
auto.
apply filter_filter_empty.
intros x.
unfold weighInv.
destruct (weigh n x).
auto.
auto.
auto.
Qed.

Definition procWorks (p:proc) := 
  forall L:coins, 
    (length L = (procDepth p)) -> 
    (exactlyn 1 L) -> 
    ((hd gold (procEval p L)) = fake).

Lemma length_cons: 
  forall A:Type, forall L:list A, forall n:nat,
    (length L) = (S n) -> exists a:A, exists L1: list A, L = (a::L1).
intros A L.
induction L.
simpl.
intros n H.
symmetry in H.
apply Nat.neq_succ_0 in H.
contradiction.
intros n Hlen.
exists a.
exists L.
reflexivity.
Qed.

Lemma list_split_length:
  forall A:Type, forall L1 L2 : list A, forall a:A,
    length (L1 ++ a::L2) = S (length (L1 ++ L2)).
  intros A L1 L2 a.
  rewrite app_length.
  rewrite app_length.
  simpl.
  rewrite plus_n_Sm.  
  reflexivity.
Qed.

Lemma In_split:
  forall A:Type, forall L1 L2:list A, forall b: A,
    In b (L1 ++ L2) -> (forall a:A, In b (L1 ++ (a::L2))).
  intros A L1 L2 b H a.
  apply in_or_app.
  apply in_app_or in H.
  decompose [or] H.
  left; exact H0.
  right.
  apply in_cons.
  exact H0.
Qed.

Lemma In_remove: 
  forall A:Type, forall L1 L2 : list A, forall a b : A,
    a<>b -> In b (L1 ++ a::L2) -> In b (L1 ++ L2).
intros A L1 L2 a b Hne Hin.
apply in_app_or in Hin.
decompose [or] Hin.
apply in_or_app; left.
exact H.
apply in_inv in H.
decompose [or] H.
elim (Hne H0).
apply in_or_app; right.
exact H0.
Qed.

Lemma NoDup_cons_inv:
  forall A:Type, forall L:list A, forall a:A,
    NoDup (a::L) -> NoDup L.
  intros A L a H.
  inversion H.
  exact H3.
Qed.

Lemma NoDup_remove_cons:
  forall A:Type, forall L: list A, forall a : A,
    NoDup (a::L) -> ~ (In a L).
intros A L a H.
replace (a::L) with ([] ++ (a::L)) in H.
apply NoDup_remove_2 in H.
simpl in H.
exact H.
simpl; reflexivity.
Qed.

Lemma list_cardinality:
  forall A:Type, forall L1 L2 : list A,
    ((forall a:A, In a L1 <-> In a L2) /\ NoDup L1 /\ NoDup L2) 
    -> (length L1 = length L2).
  intro A.
  induction L1.
  intros L2 Hand.
  decompose [and] Hand.
  destruct L2.
  reflexivity.
  absurd (In a []).
  auto.
  apply H.
  apply in_eq.
  intros L2 Hand.
  decompose [and] Hand.
  assert (Hin: In a L2).
  apply H.
  apply in_eq.
  apply in_split in Hin.
  elim Hin.
  intros L21 Hin2.
  elim Hin2; intros L22 Hsplit.
  rewrite Hsplit.
  rewrite list_split_length.
  simpl.
  f_equal.
  apply IHL1.
  apply conj.
  intros b.
  apply conj.
  decompose [and] Hand.
  intro HinL1.
  assert (HInL1_dup : In b L1).
  exact HinL1.
  apply (in_cons a) in HinL1.
  apply H0 in HinL1.
  rewrite Hsplit in HinL1.
  apply (In_remove A L21 L22 a b).
  apply NoDup_remove_cons in H4.
  intro Hne.
  rewrite Hne in H4.
  absurd (In b L1).
  exact H4.
  exact HInL1_dup.
  exact HinL1.
  intro Hb.
  assert (Hb2 : In b L2).
  rewrite Hsplit.
  apply In_split.
  exact Hb.
  remember Hb2 as Hb2'.
  clear HeqHb2'.
  apply H in Hb2.
  apply in_inv in Hb2.
  decompose [or] Hb2.
 rewrite Hsplit in Hb2'.
 rewrite Hsplit in H2.
 apply NoDup_remove_2 in H2.
 rewrite H0 in H2.
 absurd (In b (L21 ++ L22)).
 exact H2.
 exact Hb.
 exact H0.
 apply conj.
 apply NoDup_cons_inv in H1.
 exact H1.
 rewrite Hsplit in H2.
 apply NoDup_remove_1 in H2.
 exact H2.
Qed.

Definition cardinality_witness (A:Type) (P: A -> Prop) (L : list A) :=
 (forall a:A, P a <-> In a L) /\ NoDup L.

Definition cardinality (A:Type) (P: A -> Prop) (n:nat) :=
  exists L : list A, (cardinality_witness A P L) /\ (length L) = n.

Lemma cardinality_witness_unique:
  forall A:Type, forall P: A -> Prop, forall L1 L2:list A,
    ((cardinality_witness A P L1) /\ (cardinality_witness A P L2)) 
    -> (length L1 = length L2).
  intros A P L1 L2 H.
  unfold cardinality_witness in H.
  decompose [and] H.
  apply list_cardinality.
  apply conj.
  intro a.
  apply conj.
  intro HL1.
  apply H0.
  apply H2.
  exact HL1.
  intro HL2.
  apply H2.
  apply H0.
  exact HL2.
  apply conj.
  exact H3.
  exact H4.
Qed.

Lemma cardinality_unique :
forall A:Type, forall P: A -> Prop, forall n m:nat,
  (cardinality A P n) /\ (cardinality A P m) -> n = m.
  intros A P n m H.
  decompose [and] H.
  unfold cardinality in H0,H1.
  elim H0; elim H1.
  intros Lm Hm Ln Hn.
  decompose [and] Hm.
  decompose [and] Hn.
  rewrite<- H5.
  rewrite<- H3.
  apply (cardinality_witness_unique A P).
  apply conj.
  exact H4.
  exact H2.
Qed.

Lemma cardinality_coins: 
  forall n:nat,
    cardinality coins (fun L:coins => length L = n) (2^n).
intro n.
induction n.
unfold cardinality.
exists [[]].
simpl.
unfold cardinality_witness.
apply and_comm.
apply conj.
reflexivity.
apply conj.
intro a.
apply conj.
intro H.
apply length_0 in H.
rewrite H.
simpl.
left.
reflexivity.
intro H.
inversion H.
symmetry in H0.
rewrite H0.
simpl.
reflexivity.
absurd (In a []).
apply in_nil.
exact H0.
apply NoDup_cons.
apply in_nil.
apply NoDup_nil.
unfold cardinality; unfold cardinality_witness.
unfold cardinality in IHn; unfold cardinality_witness in IHn.
elim IHn.
intros L Hand.
decompose [and] Hand.
exists ((map (fun x => gold::x) L) ++ (map (fun x => fake::x) L)).
apply conj.
apply conj.
intro a.
apply conj.
intros Hlen.
assert (Hlen2: length a = S n).
exact Hlen.
apply length_cons in Hlen.
elim Hlen.
intros ahd HL1.
elim HL1.
intros atl Haeq.
apply in_or_app.
destruct ahd.
left.
rewrite Haeq.
simpl.
apply in_map.
apply (H1 atl).
rewrite Haeq in Hlen2.
simpl in Hlen2.
apply eq_add_S in Hlen2.
exact Hlen2.
right.
rewrite Haeq.
apply in_map.
rewrite Haeq in Hlen2.
simpl in Hlen2.
apply eq_add_S in Hlen2.
apply (H1 atl).
exact Hlen2.
(* Now do other direction *)
intro H.
apply in_app_or in H.
decompose [or] H.
apply in_map_iff in H3.
elim H3.
intros b.
intros H4.
decompose [and] H4.
rewrite<- H5.
simpl.
f_equal.
apply H1.
exact H6.
apply in_map_iff in H3.
elim H3.
intro b.
intros H4.
decompose [and] H4.
rewrite<- H5.
simpl.
f_equal.
apply H1.
exact H6.
(* Code for Following subgoals starts here. *)
apply NoDup_app.
apply NoDup_map.
intros a1 a2 Ha1 Ha2 Heq.
apply (f_equal (fun x : list coin => tl x)) in Heq.
simpl in Heq.
exact Heq.
exact H2.
apply NoDup_map.
intros a1 a2 Ha1 Ha2 Heq.
apply (f_equal (fun x: list coin => tl x)) in Heq.
simpl in Heq.
exact Heq.
exact H2.
intro Hand2.
elim Hand2.
intros x.
intro Hand3.
decompose [and] Hand3.
destruct x.
apply in_map_iff in H.
elim H.
intros x Hand4.
decompose [and] Hand4.
symmetry in H4.
apply nil_cons in H4.
exact H4.
destruct c.
apply in_map_iff in H3.
elim H3.
intro y.
intros Hand4.
decompose [and] Hand4.
apply (f_equal (fun x => hd gold x)) in H4.
simpl in H4.
discriminate H4.
apply in_map_iff in H.
elim H.
intros y Hand4.
decompose [and] Hand4.
apply (f_equal (fun x => hd fake x)) in H4.
simpl in H4.
discriminate H4.
rewrite app_length.
rewrite map_length.
rewrite map_length.
rewrite H0.
replace (2 ^ n + 2 ^ n) with (2 * (2 ^ n)).
rewrite<- pow_succ_r.
reflexivity.
apply le_0_n.
simpl.
rewrite<- plus_n_O.
reflexivity.
Qed.

(* Detour: Define some new list primitives to make life simpler.

*)

Fixpoint colon_helper n1 n2 :=
  match n2 with
    | 0 => []
    | S n2' => n1 :: (colon_helper (S n1) n2')
  end.

(* Colon is used to construct [1; ...; n] *)
Definition colon n := colon_helper 1 n.

Example colon_n: colon 5 = [1;2;3;4;5]. 
simpl; reflexivity.
Qed.

Lemma colon_helper_length: forall n2 n1:nat, length (colon_helper n1 n2) = n2.
  induction n2.
  intro n1.
  simpl; reflexivity.
  intro n1.
  simpl.
  f_equal.
  apply IHn2.
Qed.

Lemma colon_length: forall n:nat, length (colon n) = n.
  intro n.
  unfold colon.
  apply colon_helper_length.
Qed.

Lemma colon_helper_in:
  forall n2 n1:nat, forall m:nat,
    In m (colon_helper n1 n2) <-> m>=n1 /\ m < (n1+n2).
  induction n2.
  intros n1 m.
  simpl.
  apply conj.
  intro H; contradiction.
  intro H; decompose [and] H.
  rewrite<- plus_n_O in H1.
  absurd (m<n1).
  apply le_not_lt.
  exact H0.
  exact H1.
  intros n1 m.
  apply conj.
  simpl.
  intro H; decompose [or] H.
  rewrite<- H0.
  apply conj.
  apply le_refl.
  apply Nat.lt_add_pos_r.
  apply lt_0_Sn.
  elim (IHn2 (S n1) m).
  intros H1 H2.
  elim (H1 H0).
  intros H3 H4.
  apply conj.
  apply le_Sn_le in H3.
  exact H3.
  rewrite<- plus_Snm_nSm.
  exact H4.
  intro H; decompose [and] H.
  unfold colon_helper; fold colon_helper.
  elim (IHn2 (S n1) m).
  intros H2 H3.
  apply le_lt_n_Sm in H0.
  apply gt_S in H0.
  decompose [or] H0.
  apply in_cons.
  apply H3.
  apply conj.
  apply gt_le_S.
  exact H4.
  rewrite plus_Snm_nSm.
  exact H1.
  rewrite H4.
  apply in_eq.
Qed.

Lemma colon_in:
  forall n:nat, forall m:nat,
    In m (colon n) <-> m >= 1 /\ m <= n.
  intros n m.
  unfold colon.
  apply conj.
  intro H.
  apply colon_helper_in in H; decompose [and] H.
  apply conj.
  exact H0.
  apply lt_n_Sm_le.
  simpl in H1.
  exact H1.
  intros H; decompose [and] H.
  apply colon_helper_in.
  apply conj.
  exact H0.
  simpl.
  apply le_lt_n_Sm.
  exact H1.
Qed.

(* expand is used to create a list of the given length containing the same element. *)
Fixpoint expand (A:Type) (a:A) (n:nat) := 
  match n with
    | 0 => []
    | (S n') => a :: (expand A a n')
  end.

Lemma expand_length: forall A:Type, forall a:A, forall n:nat,
                       (length (expand A a n)) = n.
  intros A a n.
  induction n.
  simpl; reflexivity.
  unfold expand.
  fold expand.
  simpl.
  f_equal.
  apply IHn.
Qed.

Lemma expand_In: forall A:Type, forall a:A, forall n:nat,
                   forall b:A, In b (expand A a n) -> b = a.
  intros A a n.
  induction n.
  intro b.
  unfold expand.
  simpl.
  intro H; contradiction.
  intros b H.
  unfold expand in H.
  fold expand in H.
  inversion H.
  symmetry in H0; exact H0.
  apply IHn.
  exact H0.
Qed.

Lemma expand_In_inv: forall A:Type, forall a:A, forall n:nat,
                       n>0 -> In a (expand A a n).
  intros A a n.
  induction n.
  intros H.
  apply gt_irrefl in H; contradiction.
  intro H.
  unfold expand.
  simpl.
  fold expand.
  left; reflexivity.
Qed.

Lemma exactly0_expand:
  forall n:nat,
    exactlyn 0 (expand _ gold n).
  intros n.
  induction n.
  simpl.
  apply exactlyn_base.
  simpl.
  apply exactlyn_gold.
  apply IHn.
Qed.

Lemma expand_exactly0:
  forall L:coins,
    exactlyn 0 L -> L = expand _ gold (length L).
  intro L.
  induction L.
  inversion 1.
  simpl; reflexivity.
  simpl.
  inversion 1.
  f_equal.
  apply IHL.
  exact H2.
Qed.

Lemma exactly1_expand:
  forall L:coins,
    exactlyn 1 L 
    -> (exists n1 n2:nat, 
          L = (expand _ gold n1) ++ [fake] ++(expand _ gold n2)).
  intro L.
  induction L.
  intro H.
  inversion H.
  inversion 1.
  exists 0.
  exists (length L).
  simpl.
  f_equal.
  apply expand_exactly0.
  exact H2.
  simpl.
  elim (IHL H2).  
  intros n1' H4.
  elim H4.
  intro n2'.
  intro H5.
  exists (S n1').
  exists n2'.
  simpl.
  f_equal.
  exact H5.
Qed.

Lemma expand_exactly1:
  forall n1 n2:nat,
    exactlyn 1 ((expand _ gold n1) ++ [fake] ++ (expand _ gold n2)).
  induction n1. 
  simpl.
  intro n2.
  simpl.
  apply exactlyn_fake; apply exactly0_expand.
  intro n2.
  simpl.
  apply exactlyn_gold.
  apply IHn1.
Qed.

Definition exactly1_pos (len:nat) (n:nat) :=
  (expand _ gold (n-1)) ++ [fake] ++ (expand _ gold (len-n)).

Definition exactly1_gen (len:nat) :=
  map (fun n => exactly1_pos len n) (colon len).

Lemma exactly1_gen_length:
  forall len:nat, forall L:coins,
    In L (exactly1_gen len) -> (length L = len).
  intros len L H.
  unfold exactly1_gen in H.
  apply in_map_iff in H.
  elim H.
  intro c.
  intro Hand.
  decompose [and] Hand.
  apply colon_in in H1.
  decompose [and] H1.
  unfold exactly1_pos in H0.
  rewrite<- H0.
  rewrite app_length.
  rewrite app_length.
  simpl.
  rewrite expand_length.
  rewrite expand_length.
  replace (S (len -c)) with (len - (c - 1)). 
  rewrite<- le_plus_minus.
  reflexivity.
  replace (c - 1) with (pred c).
  apply Nat.le_le_pred.
  exact H3.
  simpl.
  unfold pred.
  destruct c.
  simpl; reflexivity.
  simpl.
  rewrite<- minus_n_O.
  reflexivity.
  rewrite<- (Nat.add_1_r (len - c)).
  apply (Nat.add_cancel_r _ _ (c - 1)).
  rewrite Nat.sub_add.
  rewrite<- plus_assoc.
  rewrite<- le_plus_minus.
  rewrite Nat.sub_add.
  reflexivity.
  exact H3.
  exact H2.
  apply Nat.le_sub_le_add_r.
  apply le_plus_trans.
  exact H3.
Qed.

Lemma exactly1_gen_exactly1:
  forall len:nat, forall L:coins,
    In L (exactly1_gen len) -> (exactlyn 1 L).
  intros len L H.
  unfold exactly1_gen in H.
  apply in_map_iff in H.
  elim H; intros c Hand.
  decompose [and] Hand.
  rewrite<- H0.
  unfold exactly1_pos.
  apply expand_exactly1.
Qed.

  Lemma exactly1_pos_check:
  forall len:nat, 
    (forall n:nat, (len = 0 \/ (n > len)) -> exactlyn 0 (exactly1_pos n len)) /\
    (forall n:nat, (n <= len /\ n>0) -> exactlyn 1 (exactly1_pos n len)).
induction len.
apply conj.
intros n H.
simpl.
apply exactlyn_base.
intros n H.
decompose [and] H.
apply le_not_lt in H0.
absurd (n > 0).
exact H0.
exact H1.
apply conj.
intros n Hlen.
decompose [or] Hlen.
apply Nat.neq_succ_0 in H.
contradiction.
remember H as H2.
clear HeqH2.
unfold exactly1_pos.
fold exactly1_pos.
apply Nat.lt_neq in H.
remember H as H3.
clear HeqH3.
apply<- beq_nat_false_iff in H.
rewrite Nat.eqb_sym in H.
rewrite H.
apply exactlyn_gold.
apply IHlen.
right.
apply Nat.lt_lt_pred in H2.
simpl in H2.
exact H2.
intros n H.
decompose [and] H.
unfold exactly1_pos; fold exactly1_pos.
remember (beq_nat n (S len)) as x.
destruct x.
apply exactlyn_fake.
apply IHlen.
right.
symmetry in Heqx.
apply beq_nat_true_iff in Heqx.
rewrite Heqx.
apply gt_Sn_n.
symmetry in Heqx.
apply beq_nat_false_iff in Heqx.
apply exactlyn_gold.
apply IHlen.
apply conj.
elim (Nat.le_neq n (S len)).
intros Hn1 Hn2.
apply lt_n_Sm_le.
apply Hn2.
apply conj.
exact H0.
exact Heqx.
exact H1.
Qed.

Lemma exactly1_pos_eq:
  forall len n m :nat,
    (n <= len /\ n>0) -> exactly1_pos n len = exactly1_pos m len -> n=m.
induction len.
intros n m H Hpos.
decompose [and] H.
absurd (n <= 0).
apply gt_not_le.
exact H1.
exact H0.
intros n m H Hpos.
simpl in Hpos.
remember (beq_nat n (S len)) as nx in Hpos.
remember (beq_nat m (S len)) as mx in Hpos.
symmetry in Heqnx; symmetry in Heqmx.
destruct nx.
destruct mx.
apply beq_nat_true_iff in Heqnx; apply beq_nat_true_iff in Heqmx.
rewrite Heqnx; rewrite Heqmx; reflexivity.
discriminate Hpos.
destruct mx.
apply beq_nat_false_iff in Heqnx; apply beq_nat_true_iff in Heqmx.
discriminate Hpos.
apply beq_nat_false_iff in Heqnx; apply beq_nat_false_iff in Heqmx.
apply IHlen.
decompose [and] H.
apply conj.
apply le_lt_or_eq in H0.
decompose [or] H0.
apply lt_n_Sm_le in H2.
exact H2.
absurd (n = S len).
exact Heqnx.
exact H2.
exact H1.
replace (exactly1_pos n len) with (tl (gold :: (exactly1_pos n len))).
rewrite Hpos.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Fixpoint exactly1_gen (n:nat) (len:nat) :=
  match n with
    | 0 => []
    | (S n') => (exactly1_pos n len) :: (exactly1_gen n' len)
  end
.
 
Lemma cardinality_witness_exactly1 :
  forall n:nat,
    cardinality_witness coins (fun L => (length L = n /\ exactlyn 1 L)) (exactly1_gen n n).
  intro n.
  unfold cardinality_witness.
  induction n.
  apply conj.
  intro a.
  apply conj.
  intro H; decompose [and] H.
  inversion H1.
  absurd (length a = 0).
  rewrite<- H4.
  simpl.
  auto.
  exact H0.
  absurd (length a = 0).
  rewrite<- H4; simpl; auto.
  exact H0.
  simpl.
  intro H.
  contradiction.
  simpl.
  apply NoDup_nil.
  (* Completed base case.  Now start the hard one. *)
  apply conj.
  intro a.
  apply conj.
  intro H; decompose [and] H.
  inversion H1.

Qed

Lemma cardinality_exactly1 :
  forall n:nat, 
    cardinality coins (fun L => (length L = n /\ exactlyn 1 L)) n.

Qed.

Lemma proc_bound: 
  forall p:proc, (procWorks p) -> (procDepth p) <= 3^(procCost p).
intros p Hworks.

Qed.

End Scales.
(* Local Variables: *)
(* coq-prog-name: "/usr/local/bin/coqtop" *)
(* coq-load-path: nil *)
(* End: *)