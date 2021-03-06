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

Require Import Arith.
Require Import Bool.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import List.
Require Import ListSet.
Require Import Permutation.
Require Import Psatz.

Import ListNotations.

Require Import Elementary.
Require Import Cardinality.

(** * Encoding sets of coins

We encode sets of coins as a list of coins which are either fake coins
or gold coins.

*)

Inductive coin := gold | fake.

Notation coins := (list coin).

Definition coin_weight c :=
  match c with 
    | gold => 2
    | fake => 1
  end.

(** This definition is not ideal. It limits this encoding to problems
where the relationship between the weight of the fake coins and the
gold coins is known. *)

(** ** Exactlyn *)
(* The predicate [[exactlyn]] defines valid sets with a given number
of fake coins. *)

Inductive exactlyn : nat -> coins -> Prop :=
| exactlyn_base : (exactlyn 0 nil)
| exactlyn_fake : (forall n:nat, forall ns:coins, exactlyn n ns -> exactlyn (S n) (fake::ns))
| exactlyn_gold : (forall n:nat, forall ns:coins, exactlyn n ns -> exactlyn n (gold::ns))
.

Hint Constructors exactlyn.

Ltac mini_smash := 
  repeat 
    (auto;simpl;
     match goal with
       | [ H : ?P |- ?P ] => (exact H)
       | [ |- exactlyn _ (gold :: _)] => apply exactlyn_gold
       | [ H : forall x:nat, _ -> _, _:nat |- _] => apply H
       | [ |- forall x:_, _ ] => intro x
       | [ |- (exactlyn _ _) -> _ ] => inversion 1
       | [ H : fake = ?X, H' : context[?X] |- _] => (rewrite<- H in H')
       | [ H : (exactlyn _ _) |- _ ] => (inversion H)
       | [ |- context [match ?X with | Lt => _ | Gt => _ | Eq => _ end] ] => (case X) 
       | [ |- ?X1 :: _ = ?X1 :: _ ] => f_equal
       | [ |- context [length (?X1 :: ?X2)] ] => 
         (let H := fresh "H" in
         assert (H : (length (X1 :: X2)) = S (length X2)); 
         simpl; 
         reflexivity;
         rewrite H)
      | [H : ?X1 = ?X2 |- ?X3 = ?X4 ] => rewrite H
      | [ |- _ ++ ?X1 :: _ = _ ++ ?X1 :: _ ] => f_equal
     end); 
  auto
.

Lemma exactlyn_permutes:
  forall (nsl  nsl' : coins),
    (Permutation nsl nsl') -> forall n:nat, exactlyn n nsl -> exactlyn n nsl'.
Proof.
  intros nsl nsl'; induction 1.
  auto.
  intro n; inversion 1.
  mini_smash.
  mini_smash.
  mini_smash.
  mini_smash.
Qed.

Hint Resolve exactlyn_permutes.

Lemma exactlyn_len:
  forall L:coins,  forall n:nat, exactlyn n L -> n <= (length L).
Proof.
  intro L.
  induction L.
  - mini_smash.
  - intro n.
    inversion 1.
    + apply le_n_S.
      apply IHL.
      exact H2.
    + simpl.
      apply le_S.
      apply IHL.
      exact H2.
Qed.

Lemma exactlyn_nil:
  forall n:nat, exactlyn n [] -> n = 0.
Proof.
  intro n.
  inversion 1.
  reflexivity.
Qed.

Lemma exactlyn_gold_rev:
  forall L:coins, forall n:nat, exactlyn n (gold::L) -> exactlyn n L.
Proof.
  intro.
  induction L.
  - intro n.
    inversion 1.
    exact H2.
  - intro n.
    inversion 1.
    exact H2.
Qed.

Lemma exactlyn_gold_eq: 
  forall L:coins, forall n:nat, exactlyn n (gold::L) <-> exactlyn n L.
Proof.
  intros L n.
  apply conj.
  apply exactlyn_gold_rev.
  apply exactlyn_gold.
Qed.

Lemma exactlyn_fake_rev:
  forall L:coins, forall n:nat, exactlyn n (fake::L) -> exactlyn (pred n) L.
Proof.
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
Proof.
  intros L1 n1.
  induction 1.
  - simpl.
    tauto.
  - simpl.
    intros L2 n2 Hn2.
    apply exactlyn_fake.
    apply IHexactlyn.
    exact Hn2.
  - intros L2 n2 Hn2.
    simpl.
    apply exactlyn_gold.
    apply IHexactlyn.
    exact Hn2.
Qed.

Lemma exactlyn_app_rev_simpl:
  forall L1 L2 : coins, forall n:nat, 
    exactlyn n (L1 ++ L2) -> exists n1 n2:nat, exactlyn n1 L1 /\ exactlyn n2 L2.
Proof.
  induction L1.
  - intros L2 n H.
    simpl in H.
    exists 0; exists n.
    mini_smash.
  - intros L2 n H.
    destruct a.
    + rewrite<- app_comm_cons in H.
      apply exactlyn_gold_rev in H.
      specialize (IHL1 L2 n H).
      elim IHL1.
      intro n1.
      intro H2.
      elim H2.
      intro n2.
      intro H3.
      exists n1; exists n2.
      decompose [and] H3.
      apply conj.
      * apply exactlyn_gold.
        exact H0.
      * exact H1.
    + rewrite<- app_comm_cons in H.
        apply exactlyn_fake_rev in H.
        specialize (IHL1 L2 (pred n) H).
        elim IHL1.
        intros n1 H2; elim H2; intros n2 H3.
        exists (S n1); exists n2.
        decompose [and] H3.
        apply conj.
      * apply exactlyn_fake; exact H0.
      * exact H1.
Qed.

Lemma exacltyn_app_comm:
  forall L1 L2 : coins, forall n:nat, exactlyn n (L1 ++ L2) -> exactlyn n (L2 ++ L1).
Proof.
  intros L1 L2 n.
  apply exactlyn_permutes.
  apply Permutation_app_comm.
Qed.

Lemma exactlyn_app_rev:
  forall n:nat, forall L : coins, 
    exactlyn n L
    -> forall L1 L2 : coins,
         L = L1 ++ L2 ->
         exists n1 n2:nat, (exactlyn n1 L1 /\ exactlyn n2 L2 /\ n = (n1 + n2)).
Proof.
  intros n L H.
  induction H.
  - intros L1 L2.
    intro Hnil.
    exists 0.
    exists 0.
    simpl.
    symmetry in Hnil.
    apply app_eq_nil in Hnil.
    decompose [and] Hnil.
    rewrite H; rewrite H0.
    apply conj.
    + constructor.
    + apply conj.
      constructor.
      reflexivity.
  - intros L1 L2.
    destruct L1.
    + simpl.
      intro HL2.
      rewrite<- HL2.
      exists 0.
      exists (S n).
      apply conj.
      * constructor.
      *  apply conj.
         apply exactlyn_fake.
         exact H.
         simpl.
         reflexivity.
    + rewrite <- app_comm_cons.
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
      * replace c with fake.
        apply exactlyn_fake.
        exact H2.
        change c with (hd fake (c :: L1 ++ L2)).
        rewrite <- H1.
        simpl; reflexivity.
      * apply conj.
        exact H4.
        simpl.
        f_equal.
        exact H5.
  - intros L1 L2 Happ.
    destruct L1.
    + simpl in Happ.
      exists 0.
      exists n.
      apply conj.
      constructor.
      apply conj.
      * rewrite <- Happ.
        apply exactlyn_gold.
        exact H.
      * simpl; reflexivity.
    + assert (ns = L1 ++ L2).
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
      *  replace c with gold.
         apply exactlyn_gold.
         exact H1.
         rewrite<- app_comm_cons in Happ.
         change c with (hd gold (c :: L1 ++ L2)).
         rewrite <- Happ.
         simpl; reflexivity.
      * apply conj.
        exact H3.
        exact H4.
Qed.

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

Hint Constructors proc.

(** To bring [[proc]] to life, implement a semantics for the language.
*)

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

Lemma swap_rec_fst_len:
  forall A:Type, forall L:list A, forall n m:nat,
    (length (fst (swap_rec A L n m))) = (min ((length L)-n) m).
Proof.
  intros A L.
  induction L.
  - simpl; reflexivity.
  - induction n.
    + induction m.
      * simpl; reflexivity.
      * simpl.
      f_equal.
      replace (length L) with ((length L) - 0).
      apply IHL.
      rewrite minus_n_O.
      reflexivity.
    + induction m.
      * simpl.
        apply IHL.
      * simpl.
        apply IHL.
Qed.

Lemma swap_equiv:
  forall A:Type, forall L: list A, forall n m:nat,
    (swap A L n m) = (swap_alt A L n m).
Proof.
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

Lemma swap_tl:
  forall A: Type, forall Lhd Ltl : (list A), forall n m : nat, 
    ((n+m) <= length Lhd) -> (swap A (Lhd ++ Ltl) n m) = (swap A Lhd n m) ++ Ltl.
Proof.
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

Lemma swap_app: 
  forall A:Type, forall L1 L2:list A, 
    swap A (L1 ++ L2) (length L1) (length L2) = (L2 ++ L1).
Proof.
  intros A L1 L2.
  rewrite swap_equiv.
  unfold swap_alt.
  rewrite skipn_app.
  rewrite firstn_id.
  rewrite app_assoc.
  rewrite firstn_length_app.
  rewrite<- app_length.
  rewrite<- (app_nil_r (L1 ++ L2)) at 2. 
  rewrite skipn_app.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma swap_length:
  forall A:Type, forall L: list A, forall n m:nat,
    length L = length (swap A L n m).
Proof.
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

Hint Unfold swap swap_rec.
Hint Resolve Permutation_cons Permutation_cons_app.

Lemma swap_unfold_app:
  forall L:coins, forall m:nat,
    (fst (swap_rec coin L 0 m) ++ snd (swap_rec coin L 0 m)) = (swap coin L 0 m).
Proof.
  auto.
Qed.

Hint Rewrite swap_unfold_app.

Lemma swap_permutation_app:
  forall L:coins, forall a:coin, forall m k:nat,
    Permutation L (swap coin L m k) -> Permutation (a::L) (swap coin (a::L) (S m) k).
Proof.
  intros L a m k H.
  unfold swap; simpl; apply Permutation_cons_app; exact H.
Qed.

Hint Resolve swap_permutation_app.

Lemma swap_permutes:
  forall L:coins, forall k m:nat, Permutation L (swap coin L k m).
Proof.
  induction L; auto.
  destruct k; auto.
  destruct m; auto.
  unfold swap; simpl; rewrite swap_unfold_app.
  mini_smash.
Qed.

Hint Resolve swap_permutes.

Lemma swap_swap_length_eq: 
  forall A : Type, forall L : list A, forall n m : nat,
    (length L = (n+m)) -> swap A (swap A L n m) m n = L.
Proof.
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

(** Use swap_app and breakup for case where length is equal to m+n.
   Use swap_tl for case where longer.
   This fact is not true if shorter but we don't care. *)
Lemma swap_swap_length_geq: 
  forall A : Type, forall L : list A, forall n m : nat,
    (length L >= (n+m)) -> swap A (swap A L n m) m n = L.
Proof.
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
  apply swap_swap_length_eq.
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

Lemma swap_unique: 
  forall A:Type, forall L1 L2 : list A, forall n m : nat,
    (n+m) <= (min (length L1) (length L2)) 
    -> (swap A L1 n m) = (swap A L2 n m)
    -> L1 = L2.
Proof.
  intros A L1 L2 n m Hlen Heq.
  apply Nat.min_glb_iff in Hlen.
  decompose [and] Hlen.
  rewrite<- (swap_swap_length_geq A L1 n m H).
  rewrite<- (swap_swap_length_geq A L2 n m H0).
  f_equal.
  exact Heq.
Qed.

(** ** Weigh *)

(** Sum up the weights of a set of coins. *)
Definition coin_sum (cs : coins) : nat := ListSet.set_fold_right plus (List.map coin_weight cs) 0.

Hint Unfold coin_sum set_fold_right.

Lemma sum_cons:
  forall L:coins, forall a:coin, coin_sum (a::L) = (coin_weight a) + (coin_sum L).
Proof.
  auto.
Qed.

Lemma exactlyn_sum: 
  forall L:coins, forall n:nat,
    exactlyn n L -> (coin_sum L) = n + 2 * ((length L) - n).
Proof.
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
Proof.
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

(** Pick the first n elements of the list *)
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

Lemma fst_pick_rec: 
  forall A:Type, forall L : list A, forall n:nat,
    length L = n -> fst(pick_rec A n L) = L.
Proof.
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

Lemma fst_pick_rec_tl:
  forall A:Type, forall n:nat, forall Lhd Ltl : list A, 
    (n <= length Lhd) -> fst(pick_rec A n Lhd) = fst (pick_rec A n (Lhd ++ Ltl)).
Proof.
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

Lemma fst_pick_rec_app:
  forall A:Type, forall n:nat, forall L1 L2: list A,
    (length L1) = n -> fst(pick_rec A n (L1++L2)) = L1.
Proof.
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
Proof.
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

Lemma snd_pick_rec_tl:
  forall A:Type, forall n:nat, forall Lhd Ltl : list A, 
    (n <= length Lhd) -> snd(pick_rec A n Lhd)++Ltl = snd (pick_rec A n (Lhd ++ Ltl)).
Proof.
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

Lemma snd_pick_rec_length:
  forall A:Type, forall n:nat, forall L: list A, 
    (length (snd (pick_rec A n L))) = (length L) - n.
Proof.
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

Lemma weigh_tl:
  forall n:nat, forall Lhd Ltl: coins,
    (n+n <= length Lhd) -> weigh n Lhd = weigh n (Lhd ++ Ltl).
Proof.
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

Lemma weigh_split: 
  forall n:nat, forall a:coin, forall L1 L2 :coins,
    length L1 = n -> length L2 = n  -> weigh (S n) (a::L1 ++ (a::L2)) = weigh n (L1 ++ L2).
Proof.
  intro n.
  induction n.
  intros a L1 L2 Hlen1 Hlen2.
  apply list_length0 in Hlen1.
  apply list_length0 in Hlen2.
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

Lemma weigh_defn : 
  forall n:nat, forall L1 L2 : coins, 
    length L1 = n -> 
    length L2 = n ->
    forall n1 n2 : nat,
      exactlyn n1 L1 ->
      exactlyn n2 L2 ->
      weigh n (L1 ++ L2) = nat_compare n2 n1.
Proof.
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
Proof.
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
 
(** ** Evaluation *)

(* Evaluate a weighing procedure. Given a set of coins, returns a
reordered set. This procedure is a solution if the fake coin is at the
head of the list -- indicating that it has been "found". *) 

Fixpoint procEval (p: proc) (g: coins) : coins := match p with
| Stop => g
| Swap n m p => (procEval p (swap coin g n m))
| Weigh n plt peq pgt => 
  (match weigh n g with
  | Lt => (procEval plt g)
  | Eq => (procEval peq g)
  | Gt => (procEval pgt g)
  end)
end.

(** * Properties of Procedures *)

(** Count the number of uses of a scale in a procedure. *)
Fixpoint procCost (p:proc) : nat :=
  match p with
  | Stop => 0
  | Swap _ _ p => procCost p
  | Weigh _  p1 p2 p3 => 1 + max (procCost p1) (max (procCost p2) (procCost p3))
  end.

(** Maximum size stack this procedure can observe. *)
Fixpoint procDepth (p:proc) : nat :=
  (match p with 
  | Stop => 0
  | Swap n m p => max (n+m) (procDepth p)
  | Weigh n p1 p2 p3 => max (n + n) (max (max (procDepth p1) (procDepth p2)) (procDepth p3))
  end).

Lemma procDepth_tl:
  forall p:proc, forall Lhd Ltl : coins,   
    ((procDepth p) <= (length Lhd)) -> (procEval p (Lhd++Ltl)) = (procEval p Lhd) ++ Ltl.
Proof.
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

(** * Tactical Smash

Smash is a primitive tactic inspired by Adam Chilpala's crush.  It
doesn't always work, but when it does it can eliminate some very
tedious proofs.

*)


Ltac smash := 
  repeat 
    (auto;simpl;
     match goal with
       | [ H : ?P |- ?P ] => (exact H)
       | [ |- context [swap _ _ 0 _]] => (unfold swap; simpl; rewrite swap_unfold_app)
       | [ |- exactlyn _ (gold :: _)] => apply exactlyn_gold
       | [ H : forall x:nat, _ -> _, _:nat |- _] => apply H
       | [ |- forall x:_, _ ] => intro x
       | [ |- (exactlyn _ _) -> _ ] => inversion 1
       | [ H : fake = ?X, H' : context[?X] |- _] => (rewrite<- H in H')
       | [ H : (exactlyn _ _) |- _ ] => (inversion H)
       | [ H : forall L:_, Permutation _ _ |- Permutation ?X1 (procEval _ ?X2) ] => 
             (apply Permutation_trans with (l' := X2))  
       | [ |- context [match ?X with | Lt => _ | Gt => _ | Eq => _ end] ] => (case X) 
       | [ |- ?X1 :: _ = ?X1 :: _ ] => f_equal
       | [ |- context [length (?X1 :: ?X2)] ] => 
         (let H := fresh "H" in
         assert (H : (length (X1 :: X2)) = S (length X2)); 
         simpl; 
         reflexivity;
         rewrite H)
      | [H : ?X1 = ?X2 |- ?X3 = ?X4 ] => rewrite H
      | [ |- _ ++ ?X1 :: _ = _ ++ ?X1 :: _ ] => f_equal

     end); 
  auto.


(** * Correctness 

For [[proc]] to be a valid encoding of the intended problem it is
important that procedures cannot manufacture coins or otherwise
cheat. To encode this correctness criteria establish that the output
is always a permutation of the input.

*)

(** ** Basic properties of [[procEval]] *)

Lemma procEval_permutes:
  forall p:proc, forall L : coins, Permutation L  (procEval p L).
Proof.
  induction p.
  smash.
  smash.
  smash.
Qed.

Lemma procEval_length:
  forall p:proc, forall L:coins, (length L) = (length (procEval p L)).
Proof.
  intros p L.
  apply Permutation_length.
  apply procEval_permutes.
Qed.

Hint Rewrite procEval_length.

(** ** Example solution for 4 and 12 coins *)

(* Given 4 coins where one is fake. Find the fake one. [[p4] encodes a
solution to this problem. Proof below. *)

Definition p4 : proc :=
   (Weigh 1 
       Stop 
        (Swap 2 2 (Weigh 1 Stop Stop (Swap 1 1 Stop)))
        (Swap 1 1 Stop)).

Example p4Example1:
  procEval p4 [gold;gold;fake;gold] = [fake;gold;gold;gold].
Proof.
  compute.
  reflexivity.
Qed.

(** Given twelve coins where one is lighter, Find the lighter one.
[[p12]] is a solution to this problem (proof below). *)
Definition p12 : proc :=
    (Weigh 4
        p4
         (Swap 8 4 p4)
         (Swap 4 4 p4)).

(** Examples used to test the proposed solution. *)
Definition ex1 : coins := [gold;gold;gold;gold; gold;gold;gold;gold; gold;gold;gold;fake].
Definition ex2 : coins := [gold;fake;gold;gold; gold;gold;gold;gold; gold;gold;gold;gold].
Definition ex3 : coins := [gold;gold;gold;gold; gold;gold;fake;gold; gold;gold;gold;gold].


(* Now verify that p12 behaves as expected. *)
Eval cbv in (procEval p12 ex1).
Eval cbv in (procEval p12 ex2).
Eval cbv in (procEval p12 ex3).

Eval simpl in (procCost p12).

(** ** Proof that [[p4]] Works *)

(* Now apply all of this hard earned knowledge to prove that [[p4]] works. *)
Corollary p4_works:
  forall L: coins,
    (length L = 4)
    -> (exactlyn 1 L)
    -> ((hd gold (procEval p4 L)) = fake).
Proof.
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

(** ** Proof that [[p12]] works *)

Lemma p12_depth:
  procDepth p12 = 12.
Proof.
  auto.
Qed.

Lemma p12_works:
  forall ns :coins,
    (length ns = 12)
    -> (exactlyn 1 ns)
    -> ((hd gold (procEval p12 ns)) = fake).
Proof.
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
  rewrite p4_works.
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
  rewrite p4_works.
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
  apply p4_works.
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

(** * Inverse execution of [[proc]].

  This sections defines an evaluator that runs [[proc]] in reverse.
  It returns every possible input that could produce the given set of
  outputs.

  Inverse exeuction will be useful for arguing about optimal solutions.

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
Proof.
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

(** First show that procEvalInv contains all possible inputs. Call
this property being full. *)

Lemma procEvalInv_is_full :
  forall p:proc,forall g:coins, 
    (procDepth p <= length g) -> 
    (List.In g (procEvalInv p [procEval p g])).
Proof.
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
  rewrite swap_swap_length_geq.
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
Proof.
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

(** Show that procEvalInv is an inverse.  *)
Lemma procEvalInv_is_inverse : 
  forall p:proc, forall g gInv:coins,
    (procDepth p <= length g) ->
    In gInv (procEvalInv p [g]) -> 
    procEval p gInv = g.
Proof.
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
  rewrite swap_swap_length_geq.
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

Theorem procEvalInv_is_full_inverse:
  forall p:proc, forall g gInv:coins,
    (procDepth p <= length g) -> 
    ((In gInv (procEvalInv p [g])) <-> (procEval p gInv = g)).
Proof.
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

(** The proof establishes that procEvalInv is a real inverse function.
Now it remains to show that the output of procEvalInv has no
duplicates, and to bound the number of elements in the output of
procEvalInv. *)

(** This lemma shows that the inverse function produces less than 3 *
(the number of uses of the scale). For a procedure to work, it must
produce every possible input from the one correct output. *)

Lemma procEvalInv_length_bound: 
  forall p:proc, forall g:coins,
    length (procEvalInv p [g]) <= 3 ^ (procCost p).
Proof.
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

(** The goal of this argument is to place a bound on the number of
weighings that are needed.  To do so, first prove that the inverse
function does not contain duplicates.  *)

Lemma procEvalInv_NoDup: 
  forall p : proc, forall L : list coins,
    (forall x:coins, In x L -> (procDepth p <= (length x)))
    -> NoDup L 
    -> NoDup (procEvalInv p L).
Proof.
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

(** ** procWorks 

  procWorks defines a generic predict that defines what we mean for a
  procedure to be correct.

 *)

Definition procWorks (p:proc) := 
  forall L:coins, 
    (length L = (procDepth p)) -> 
    (exactlyn 1 L) -> 
    ((hd gold (procEval p L)) = fake).


(** There are 2^n possible combinations of fake and real coins.
*)
Lemma cardinality_coins: 
  forall n:nat,
    cardinality coins (fun L:coins => length L = n) (2^n).
Proof.
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
  apply list_length0 in H.
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
  rewrite<- Nat.pow_succ_r.
  reflexivity.
  apply le_0_n.
  simpl.
  rewrite<- plus_n_O.
  reflexivity.
Qed.

(** ** List primitives (Detour)

*)

Fixpoint colon_helper n1 n2 :=
  match n2 with
    | 0 => []
    | S n2' => n1 :: (colon_helper (S n1) n2')
  end.

(* Colon is used to construct [1; ...; n] *)
Definition colon n := colon_helper 1 n.

Example colon_n:
  colon 5 = [1;2;3;4;5]. 
Proof.
  simpl; reflexivity.
Qed.

Lemma colon_helper_length:
  forall n2 n1:nat, length (colon_helper n1 n2) = n2.
Proof.
  induction n2.
  intro n1.
  simpl; reflexivity.
  intro n1.
  simpl.
  f_equal.
  apply IHn2.
Qed.

Lemma colon_length:
  forall n:nat, length (colon n) = n.
Proof.
  intro n.
  unfold colon.
  apply colon_helper_length.
Qed.

Lemma colon_helper_in:
  forall n2 n1:nat, forall m:nat,
    In m (colon_helper n1 n2) <-> m>=n1 /\ m < (n1+n2).
Proof.
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
Proof.
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

Lemma colon_helper_nodup:
  forall m n:nat, NoDup (colon_helper n m).
Proof.
  induction m.
  simpl.
  intro.
  apply NoDup_nil.
  simpl.
  intro n.
  apply NoDup_cons.
  intro.
  apply colon_helper_in in H.
  lia.
  apply IHm.
Qed.

Lemma colon_nodup:
  forall n:nat, NoDup (colon n).
Proof.
  intro n.
  unfold colon.
  apply colon_helper_nodup.
Qed.

(* [[expand]] is used to create a list of the given length containing the
same element repeatedly. *)

Fixpoint expand (A:Type) (a:A) (n:nat) := 
  match n with
    | 0 => []
    | (S n') => a :: (expand A a n')
  end.

Lemma expand_length:
  forall A:Type, forall a:A, forall n:nat,
    (length (expand A a n)) = n.
Proof.
  intros A a n.
  induction n.
  simpl; reflexivity.
  unfold expand.
  fold expand.
  simpl.
  f_equal.
  apply IHn.
Qed.

Lemma expand_app:
  forall A:Type, forall c:A, forall n:nat,
    expand A c (S n) = expand A c n ++ [c].
Proof.
  intros A c n.
  induction n.
  simpl; reflexivity.
  unfold expand.
  fold expand.
  unfold expand in IHn.
  fold expand in IHn.
  rewrite<- app_comm_cons.
  rewrite<- IHn.
  f_equal.
Qed.

Lemma expand_nil:
  forall A:Type, forall a:A, expand A a 0 = [].
Proof.
  intros A a.
  unfold expand.
  reflexivity.
Qed.

Lemma expand_Sn: 
  forall A:Type, forall a:A, forall n:nat, 
    expand A a (S n) = a :: (expand A a n).
Proof.
  intros A a n.
  unfold expand at 1.
  fold expand.
  reflexivity.
Qed.

Lemma expand_plus:
  forall A:Type, forall a:A, forall n m:nat,
    (expand A a (n + m)) = (expand A a n) ++ (expand A a m).
Proof.
  intros A a n m.
  induction n.
  rewrite expand_nil.
  simpl.
  reflexivity.
  rewrite expand_Sn.
  replace (S n + m) with (S (n+m)).
  rewrite expand_Sn.
  rewrite IHn.
  reflexivity.
  ring.
Qed.

Lemma expand_In:
  forall A:Type, forall a:A, forall n:nat,
  forall b:A, In b (expand A a n) -> b = a.
Proof.
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

Lemma expand_In_inv:
  forall A:Type, forall a:A, forall n:nat,
    n>0 -> In a (expand A a n).
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
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

Hint Resolve expand_exactly1.

Definition exactly1_pos (len:nat) (n:nat) :=
  (expand _ gold n) ++ [fake] ++ (expand _ gold (len-n-1)).

Lemma exactly1_pos_length:
  forall len n : nat,
    len > n -> length (exactly1_pos len n) = len.
Proof.
  smash.
  
  unfold exactly1_pos.
  rewrite app_length.
  rewrite app_length.
  simpl.
  rewrite expand_length.
  rewrite expand_length.
  rewrite Nat.sub_1_r.
  rewrite Nat.succ_pred_pos.
  rewrite le_plus_minus_r.
  reflexivity.
  decompose [and] x.
  apply lt_le_weak.
  exact x.
  rewrite (minus_diag_reverse n).
  apply (plus_lt_reg_l (n-n) (len - n) n).
  rewrite le_plus_minus_r.
  rewrite le_plus_minus_r.
  exact x.
  apply lt_le_weak.
  exact x.
  reflexivity.
Qed.

Lemma exactly1_pos_length_degenerate:
  forall len n : nat,
    n >= len -> length (exactly1_pos len n) = (n+1).
Proof.
  intros len n H.
  unfold exactly1_pos.
  replace (len-n-1) with 0.
  simpl.
  rewrite app_length.
  simpl.
  f_equal.
  apply expand_length.
  lia.
Qed.

Lemma exactly1_pos_exactly1:
  forall len n:nat,
    n < len -> exactlyn 1 (exactly1_pos len n).
Proof.
  intros len n Hlen.
  unfold exactly1_pos.
  apply (exactlyn_app (expand coin gold n) 0).
  apply exactly0_expand.
  apply (exactlyn_app [fake] 1).
  smash.
  apply exactly0_expand.
Qed.

Definition exactly1_gen (len:nat) :=
  map (fun n => exactly1_pos len (n-1)) (colon len).

Lemma exactly1_gen_length:
  forall len:nat,
    length (exactly1_gen len) = len.
Proof.
  smash.
  unfold exactly1_gen.
  rewrite map_length.
  rewrite colon_length.
  reflexivity.
Qed.

Lemma exactly1_gen_sub_lengths:
  forall len:nat, forall L:coins,
    In L (exactly1_gen len) -> (length L = len).
Proof.
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
  lia.
Qed.

Lemma exactly1_gen_exact:
  forall len:nat, forall L:coins,
    In L (exactly1_gen len) -> (exactlyn 1 L).
Proof.
  intros len L H.
  unfold exactly1_gen in H.
  apply in_map_iff in H.
  elim H; intros c Hand.
  decompose [and] Hand.
  rewrite<- H0.
  unfold exactly1_pos.
  apply expand_exactly1.
Qed.

Lemma exactly1_pos_last:
  forall n:nat,
    exactly1_pos (S n) n = (expand _ gold n) ++ [fake].
Proof.
  intros n.
  unfold exactly1_pos.
  replace (S n - n - 1) with 0.
  simpl.
  reflexivity.
  lia.
Qed.

Lemma exactly1_pos_S: 
  forall len n:nat,
    (n < len) -> (exactly1_pos (S len) n) = ((exactly1_pos len n) ++ [gold]).
Proof.
  intros len n Hlen.
  unfold exactly1_pos.
  simpl.
  rewrite<- app_assoc.
  f_equal.
  rewrite<- app_comm_cons.
  f_equal.
  destruct n.
  simpl.
  replace (len - 0) with len.
  rewrite<- expand_app.
  replace (S (len - 1)) with len.
  reflexivity.
  lia.
  lia.
  rewrite<- expand_app.
  replace (S (len - S n - 1)) with (len - n - 1).
  reflexivity.
  lia.
Qed.

Lemma exactly1_pos_eq:
  forall len n m :nat,
    (n < len) -> exactly1_pos len n = exactly1_pos len m -> n=m.
Proof.
  induction len.
  intros n m Hlen Hpos.
  absurd (n<0).
  lia.
  exact Hlen.
  intros n m Hlen Hpos.
  assert (Hpos_len:length (exactly1_pos (S len) n) = length (exactly1_pos (S len) m)).
  rewrite Hpos; reflexivity.
  rewrite (exactly1_pos_length _ _ Hlen) in Hpos_len.
  assert (Hm_len: m < (S len)).
  assert (Hcases: (m < (S len) \/ m >= (S len))).
  apply Nat.lt_ge_cases.
  decompose [or] Hcases.
  exact H.
  rewrite (exactly1_pos_length_degenerate _ _ H) in Hpos_len.
  rewrite Hpos_len in H.
  absurd (m >= m + 1).
  lia.
  exact H.
  clear Hpos_len.
  assert (n<len \/ n = len).
  lia.
  decompose [or] H.
  rewrite (exactly1_pos_S _ _ H0) in Hpos.
  assert (m<len \/ m = len).
  lia.
  decompose [or] H1.
  rewrite (exactly1_pos_S _ _ H2) in Hpos.
  apply app_inv_tail in Hpos.
  apply (IHlen _ _ H0 Hpos).
  rewrite H2 in Hpos.
  rewrite exactly1_pos_last in Hpos.
  assert (Hbogus: length [gold] = length [fake]).
  simpl; reflexivity.
  apply length_app_eq_snd in Hpos.
  discriminate Hpos.
  right; exact Hbogus.
  rewrite H0 in Hpos.
  rewrite exactly1_pos_last in Hpos.
  assert (m = len \/ m < len).
  lia.
  decompose [or] H1.
  rewrite H0; rewrite H2; reflexivity.
  rewrite (exactly1_pos_S _ _ H2) in Hpos.
  apply length_app_eq_snd in Hpos.
  discriminate Hpos.
  right; simpl; reflexivity.
Qed.

Lemma exactly1_gen_NoDup:
  forall n:nat, NoDup (exactly1_gen n).
Proof.
  intro n.
  induction n.
  unfold exactly1_gen.
  simpl.
  apply NoDup_nil.
  unfold exactly1_gen.
  apply NoDup_map.
  intros a1 a2 Ha1 Ha2 Hex.
  apply colon_in in Ha1.
  apply colon_in in Ha2.
  decompose [and] Ha1.
  decompose [and] Ha2.
  clear Ha1 Ha2.
  apply exactly1_pos_eq in Hex.
  lia.
  lia.
  apply colon_nodup.
Qed.

Lemma exactly1_gen_combo:
  forall n:nat, forall a:coins,
    In a (exactly1_gen (S n)) -> In (gold::a) (exactly1_gen (S (S n))).
Proof.
  intros n a.
  unfold exactly1_gen.
  intro H.
  apply List.in_map_iff.
  apply List.in_map_iff in H.
  elim H.
  clear H.
  intro x.
  intro H.
  exists (S x).
  replace (S x - 1) with x.
  decompose [and] H.
  clear H.
  apply colon_in in H1.
  apply conj.
  unfold exactly1_pos.
  unfold exactly1_pos in H0.
  rewrite<- H0.
  rewrite app_comm_cons.
  rewrite<- expand_Sn.
  replace (S (x - 1)) with x.
  replace (S n - (x - 1) - 1) with (S (S n) - x - 1).
  reflexivity.
  lia.
  lia.
  apply colon_in.
  lia.
  lia.
Qed.

Lemma cardinality_witness_exactly1 :
  forall n:nat,
    (cardinality_witness
       coins
       (fun L => (length L = (S n) /\ exactlyn 1 L))
       (exactly1_gen (S n))).
Proof.
  induction n.
  
(* Case n = 0 *)
  unfold cardinality_witness.
  unfold exactly1_gen.
  unfold colon.
  unfold colon_helper.
  simpl.
  apply conj.
  intro a.
  apply conj.
  intro H.
  left.
  unfold exactly1_pos.
  simpl.
  decompose [and] H.
  inversion H1.
  rewrite<- H4 in H0.
  simpl in H0.
  apply eq_add_S in H0.
  apply list_length0 in H0.
  rewrite H0.
  reflexivity.
  rewrite<- H4 in H0.
  simpl in H0.
  apply eq_add_S in H0.
  apply list_length0 in H0.
  rewrite H0 in H2.
  inversion H2.
  smash.
  decompose [or] x.
  unfold exactly1_pos in H.
  simpl in H.
  rewrite<- H.
  smash.
  contradiction.
  unfold exactly1_pos.
  simpl.
  apply NoDup_cons.
  auto.
  apply NoDup_nil.

  (* Inductive case. *)
  unfold cardinality_witness.
  apply conj.
  intro a.
  apply conj.
  intro L.
  decompose [and] L.
  clear L.
  unfold cardinality_witness in IHn.
  decompose [and] IHn.
  clear IHn.
  induction a.
  simpl in H.
  contradict H.
  lia.
  destruct a.
  apply exactly1_gen_combo.
  elim H1 with a0.
  intros H3 H4.
  simpl in H.
  clear IHa.
  apply H3.
  apply conj.
  auto.
  apply exactlyn_gold_rev.
  exact H0.
  unfold exactly1_gen.
  unfold colon.
  simpl.
  left.
  unfold exactly1_pos.
  simpl.
  apply exactlyn_fake_rev in H0.
  simpl in H0.
  apply expand_exactly0 in H0.
  rewrite H0.
  replace (length a0) with (S n).
  rewrite expand_Sn.
  reflexivity.
  simpl in H.
  lia.
  intro H.
  apply conj.
  apply exactly1_gen_sub_lengths in H.
  exact H.
  apply exactly1_gen_exact in H.
  exact H.
  apply exactly1_gen_NoDup.
Qed.

Lemma cardinality_exactly1:
  forall n:nat, 
    cardinality coins (fun L => (length L = n /\ exactlyn 1 L)) n.
Proof.
  intro n.
  unfold cardinality.
  destruct n.
  exists [].
  simpl.
  apply conj.
  unfold cardinality_witness.
  simpl.
  apply conj.
  intro a.
  apply conj.
  intro H.
  decompose [and] H.
  apply list_length0 in H0.
  rewrite H0 in H1.
  apply exactlyn_nil in H1.
  lia.
  intro H.
  contradiction.
  apply NoDup_nil.
  reflexivity.
  exists (exactly1_gen (S n)).
  apply conj.
  apply cardinality_witness_exactly1.
  apply exactly1_gen_length.
Qed.

Definition sorted_coins n := 
  match n with 
    | 0 => []
    | (S m) => fake :: (expand coin gold m)
  end.

Lemma sorted_coins_length:
  forall n:nat,
    length (sorted_coins n) = n.
Proof.
  intro n.
  induction n.
  simpl.
  ring.
  unfold sorted_coins.
  simpl.
  rewrite expand_length.
  reflexivity.
Qed.

Fixpoint sift (L:coins) :=
  match L with
    | [] => ([], [])
    | (a::b) => 
           match a with
             | gold => (gold::(fst (sift b)),(snd (sift b)))
             | fake => ((fst (sift b)),fake::(snd (sift b)))
           end
  end.

Lemma exactlyn_sifted:
  forall n:nat, forall L:coins,
    exactlyn n L -> 
    exactlyn 0 (fst (sift L)) /\ exactlyn n (snd (sift L)) /\ Permutation ((fst (sift L))++(snd (sift L))) L.
Proof.
  intros n L.
  induction 1.
  simpl.
  auto.
  decompose [and] IHexactlyn.
  unfold sift.
  simpl.
  fold sift.
  apply conj.
  exact H0.
  apply conj.
  apply exactlyn_fake.
  exact H2.
  apply Permutation_sym.
  apply Permutation_cons_app.
  apply Permutation_sym.
  exact H3.
  decompose [and] IHexactlyn.
  apply conj.
  simpl.
  apply exactlyn_gold.
  exact H0.
  apply conj.
  simpl.
  exact H2.
  simpl.
  apply perm_skip.
  exact H3.
Qed.

Lemma exactlyn_0_eq:
  forall L1 L2:coins,
    (length L1 = length L2) -> exactlyn 0 L1 -> exactlyn 0 L2 -> L1 = L2.
Proof.
  induction L1.
  simpl.
  intros L2 Hlen Hex1 Hex2.
  symmetry in Hlen.
  apply list_length0 in Hlen.
  rewrite Hlen.
  reflexivity.
  destruct L2.
  intro Hlen.
  simpl in Hlen.
  lia.
  simpl.
  intro Hlen.
  apply eq_add_S in Hlen.
  inversion 1.
  inversion 1.
  f_equal.
  apply (IHL1 _ Hlen H2 H7).
Qed.

Lemma exactlyn_n_eq:
  forall L1 L2:coins,
    (length L1 = length L2) -> 
    exactlyn (length L1) L1 ->
    exactlyn (length L2) L2 ->
    L1 = L2.
Proof.
  induction L1.
  intros L2 Hlen.
  simpl in Hlen.
  symmetry in Hlen.
  apply list_length0 in Hlen.
  rewrite Hlen.
  auto.
  destruct L2.
  intro Hlen.
  simpl in Hlen.
  lia.
  simpl.
  intro Hlen.
  apply eq_add_S in Hlen.
  inversion 1.
  inversion 1.
  f_equal.
  apply (IHL1 _ Hlen H2 H7).
  rewrite<- H5 in H4.
  apply exactlyn_gold_rev in H4.
  apply exactlyn_len in H4.
  apply le_Sn_n in H4.
  contradict H4.
  inversion 1.
  apply exactlyn_len in H2.
  apply le_Sn_n in H2.
  contradict H2.
  f_equal.
  rewrite<- H0 in H.
  apply exactlyn_gold_rev in H.
  apply exactlyn_len in H.
  apply le_Sn_n in H.
  contradict H.
Qed.

Lemma exactlyn_sifted_fst_length:
  forall n:nat, forall L:coins,
    exactlyn n L -> (length (fst (sift L))) = (length L) - n.
Proof.
  intros n L Hex.
  induction Hex.
  simpl.
  auto.
  simpl.
  exact IHHex.
  simpl (fst (sift (gold :: ns))).
  simpl (length _).
  apply exactlyn_len in Hex.
  lia.
Qed.

Lemma exactlyn_sifted_snd_length:
  forall n:nat, forall L:coins,
    exactlyn n L -> (length (snd (sift L))) = n.
Proof.
  induction n.
  intros L Hex.
  simpl.
  induction Hex.
  auto.
  simpl.
  lia.
  simpl.
  exact IHHex.
  intros L Hex.
  induction Hex.
  auto.
  simpl.
  auto.
  simpl.
  auto.
Qed.

Lemma exactlyn_inv_permutes:
  forall L1 L2:coins,     
    length L1 = length L2 ->
    forall n:nat,
      exactlyn n L1 -> 
      exactlyn n L2 -> 
      Permutation L1 L2.
Proof.
  intros L1 L2 Hlen n Hex1 Hex2.
  assert (Hsift1 := exactlyn_sifted _ _ Hex1).
  decompose [and] Hsift1.
  clear Hsift1.
  assert (Hsift2 := exactlyn_sifted _ _ Hex2).
  decompose [and] Hsift2.
  clear Hsift2.
  apply perm_trans with (l':= (fst (sift L1) ++ snd (sift L1))).
  apply Permutation_sym.
  exact H2.
  apply Permutation_sym in H2.
  assert (Hfsteq : (fst (sift L1) = fst (sift L2))).
  apply exactlyn_0_eq.
  rewrite (exactlyn_sifted_fst_length _ _ Hex1).
  rewrite (exactlyn_sifted_fst_length _ _ Hex2).
  lia.
  auto.
  auto.
  assert (Hsndeq: (snd (sift L1) = snd (sift L2))).
  apply exactlyn_n_eq.
  rewrite (exactlyn_sifted_snd_length _ _ Hex1).
  rewrite (exactlyn_sifted_snd_length _ _ Hex2).
  auto.
  rewrite (exactlyn_sifted_snd_length _ _ Hex1).
  exact H1.
  rewrite (exactlyn_sifted_snd_length _ _ Hex2).
  exact H4.
  rewrite Hfsteq.
  rewrite Hsndeq.
  exact H5.
Qed.

Lemma exactly1_gen_permutes:
  forall n:nat, forall L1: coins,
    In L1 (exactly1_gen n) -> (forall L2:coins, Permutation L1 L2 <-> In L2 (exactly1_gen n)).
Proof.
  intro n.
  induction n.
  simpl.
  firstorder.
  intros L1 H.
  intro L2.
  assert (HL1 : length L1 = (S n)).
  apply exactly1_gen_sub_lengths in H.
  exact H.
  apply conj.
  intro Hp.
  assert (HL2 : length L2 = (S n)).
  apply Permutation_length in Hp.
  rewrite<- Hp.
  exact HL1.
  apply exactly1_gen_exact in H.
  apply exactlyn_permutes with (n:=1) in Hp.
  elim (cardinality_witness_exactly1 n).
  intro Hc.
  intro Hdup.
  apply Hc.
  apply conj.
  exact HL2.
  exact Hp.
  exact H.
  intro Hex2.
  assert (HL2 : length L2 = (S n)).
  apply exactly1_gen_sub_lengths in Hex2.
  exact Hex2.  
  apply exactly1_gen_exact in H.
  apply exactly1_gen_exact in Hex2.
  assert (Hlen: length L1 = length L2).
  lia.
  apply (exactlyn_inv_permutes _ _ Hlen 1 H Hex2).
Qed.

Lemma exacltyn_1_sorts:
  forall L:coins,
    exactlyn 1 L ->
    Permutation L (sorted_coins (length L)).
Proof.
  intros L Hex.
  assert (Hlen : length L > 0).
  apply exactlyn_len.
  exact Hex.
  assert (H : exactlyn 1 (sorted_coins (length L))).
  destruct L.
  simpl in Hlen.
  lia.
  unfold sorted_coins.
  simpl.
  apply exactlyn_fake.
  apply exactly0_expand.
  assert (Hslen: length L = length (sorted_coins (length L))).
  rewrite sorted_coins_length.
  auto.
  apply (exactlyn_inv_permutes L (sorted_coins (length L)) Hslen 1).
  exact Hex.
  exact H.
Qed.

Lemma procEval_sorts:
  forall p:proc, 
    (procWorks p) ->
    forall L:coins, 
      (length L = procDepth p) ->
      exactlyn 1 L -> 
      (procEval p L) = (sorted_coins (length L)). 
Proof. 
  intros p Hworks L Hlen Hex.
  assert (Hperm := (procEval_permutes p L)).
  unfold procWorks in Hworks.
  assert (H := Hworks L Hlen Hex).
  destruct L.
  apply exactlyn_nil in Hex.
  lia.
  simpl.
  unfold hd in H.
  destruct (procEval p (c::L)).
  apply Permutation_sym in Hperm.
  apply Permutation_nil in Hperm.
  symmetry in Hperm.
  apply nil_cons in Hperm.
  contradiction Hperm.
  rewrite H.
  f_equal.
  rewrite H in Hperm.
  clear H c0.
  assert (Hex2:= (exactlyn_permutes (c::L) (fake::l) Hperm 1 Hex)).
  apply exactlyn_fake_rev in Hex2.
  simpl in Hex2.
  apply Permutation_length in Hperm.
  simpl in Hperm.
  apply eq_add_S in Hperm.
  rewrite Hperm.
  exact (expand_exactly0 l Hex2).
Qed.

Lemma proc_works_inv:
  forall p:proc, 
    (procDepth p) > 0 ->
    (procWorks p) -> 
    (Permutation (procEvalInv p [sorted_coins (procDepth p)]) (exactly1_gen (procDepth p))).
Proof.
  intros p Hdepth Hworks.
  assert (Hcardw := (cardinality_witness_exactly1 (pred (procDepth p)))).
  assert (Hsize : S (pred (procDepth p)) = (procDepth p)).
  lia.
  rewrite Hsize in Hcardw.
  clear Hsize.
  unfold cardinality_witness in Hcardw.
  elim Hcardw.
  intros Hcard Hnodup.
  clear Hcardw.
  apply NoDup_Permutation.
  apply procEvalInv_NoDup.
  intros x H.
  apply In_one in H.
  rewrite<- H.
  rewrite sorted_coins_length.
  lia.
  apply NoDup_cons.
  intro.
  apply List.in_nil in H.
  contradiction.
  apply NoDup_nil.
  apply exactly1_gen_NoDup.
  intro x.
  apply conj.
  intro H.
  apply procEvalInv_is_inverse in H.
  assert (Hcardx := (Hcard x)).
  apply Hcardx.
  clear Hcard.
  apply conj.
  assert (Hlen := (procEval_length p x)).
  rewrite Hlen.
  rewrite H.
  rewrite (sorted_coins_length _).
  reflexivity.
  assert (Hperm : Permutation x (sorted_coins (procDepth p))).
  rewrite<- H.
  apply procEval_permutes.
  apply Permutation_sym in Hperm.
  apply (exactlyn_permutes _ _ Hperm 1).
  unfold sorted_coins.
  destruct (procDepth p).
  lia.
  apply exactlyn_fake.
  apply exactly0_expand.
  rewrite sorted_coins_length.
  lia.
  intro Hgen.
  assert (Hcardx := (Hcard x)).
  clear Hcard.
  apply procEvalInv_is_full_inverse.
  rewrite sorted_coins_length.
  lia.
  assert (H : (length x = procDepth p /\ exactlyn 1 x)).
  apply Hcardx.
  apply Hgen.
  decompose [and] H.
  rewrite<- H0.
  apply (procEval_sorts p Hworks x H0 H1).
Qed.

(** * Establishing a bound

  This section finally establishes a bound on the number of uses of
  the scale for a given number of coins.  The proof relies on the
  inverse function, and the cardinality arguments established in the
  prior sections.

 *)

Theorem proc_bound: 
  forall p:proc, (procWorks p) -> (procDepth p) <= 3^(procCost p).
Proof.
  intros p Hworks.
  remember (procDepth p) as n.
  destruct n.
  lia.
  assert (Hdepth: procDepth p > 0).
  lia.
  assert (Hperm := (proc_works_inv p Hdepth Hworks)).
  assert (Hbound := procEvalInv_length_bound p (sorted_coins (procDepth p)) ).
  assert (Hlen : (length (procEvalInv p [sorted_coins (procDepth p)]) = procDepth p)).
  apply Permutation_length in Hperm.
  rewrite Hperm in Hbound.
  rewrite Hperm.
  rewrite exactly1_gen_length.
  reflexivity.
  rewrite Hlen in Hbound.
  rewrite Heqn.
  exact Hbound.
Qed.

(** * An Optimal Procedure 

  This section defines an optimal procedure for any number of coins.
  It culminates with a proof that no working procedure can use the
  scale less than this one.

*)
Require Import Recdef.

Lemma weigh_exactlyn: 
  forall L1 L2 L3 : coins, 
    length L1 = length L2 -> 
    exactlyn 1 ((L1 ++ L2) ++ L3) ->
    match weigh (length L1) ((L1 ++ L2) ++ L3) with
      | Lt => exactlyn 1 L1
      | Eq => exactlyn 1 L3
      | Gt => exactlyn 1 L2
    end.
Proof.
  intros L1 L2 L3 Hlen Hex.
  
  assert (H1 := (exactlyn_app_rev 1 _ Hex (L1++L2) L3)).
  destruct H1 as [n1].
  reflexivity.
  destruct H as [n2].
  decompose [and] H.
  clear H.
  assert (Hex2 := (exactlyn_app_rev n1 _ H0 L1 L2)).
  destruct Hex2 as [n3].
  reflexivity.
  destruct H as [n4].
  decompose [and] H.
  clear H.
  assert (Hlen2: length L1 + length L1 <= length (L1 ++ L2)).
  rewrite app_length.
  lia.
  rewrite<- (weigh_tl (length L1) (L1 ++ L2) L3 Hlen2).
  symmetry in Hlen.
  assert (Hduh : length L1 = length L1).
  reflexivity.
  rewrite (weigh_defn (length L1) L1 L2 Hduh Hlen n3 n4 H1 H5).
  
  (* Now we have reduced this to a nat_compare problem. *)
  remember (nat_compare n4 n3) as R.
  symmetry in HeqR.
  
  destruct R.
  rewrite H6 in H3.
  
  apply nat_compare_eq_iff in HeqR.
  
  assert (H: n2 = 1).
  lia.
  rewrite H in H2.
  exact H2.
  
  apply nat_compare_lt in HeqR.
  assert (H: n3 = 1).
  lia.
  rewrite H in H1.
  exact H1.
  
  apply nat_compare_gt in HeqR.
  assert (H: n4 = 1).
  lia.
  rewrite H in H5.
  exact H5.
Qed.

(** 

  Define a higher-order function that applies the divide-and-conquer
  approach.  [procSplit] takes working procedures for different
  lengths, and then applies those procedures to different sets of
  coins.

  The [procSplit] procedure defines a simple decision tree.  First
  weight the first "dw" coins against the next "dw" coins with "drest"
  leftover.  If the two "dw" sets have the same weight then the fake
  is in "drest".  Otherwise, it is in the lighter "dw" set.

 *)
Definition procSplit (pdw pdrest : proc) :=
  let dw := procDepth pdw in
  let drest := procDepth pdrest in
  (Weigh dw 
         pdw
         (Swap (dw + dw) drest pdrest) 
         (Swap dw dw pdw)).

Lemma procSplit_depth: 
  forall pdw pdrest : proc, 
  let dw := procDepth pdw in
  let drest := procDepth pdrest in
    procDepth (procSplit pdw pdrest) = dw + dw + drest.
Proof.
  intros pdw pdrest dw drest.
  unfold procSplit.
  simpl.
  fold dw.
  fold drest.
  rewrite (Max.max_l (dw + dw) dw).
  rewrite (Max.max_l (dw + dw + drest) drest).
  rewrite (Max.max_r dw (dw + dw + drest)).
  rewrite (Max.max_l (dw + dw + drest) (dw + dw)).
  rewrite (Max.max_r _ _).
  reflexivity.
  lia.
  lia.
  lia.
  lia.
  lia.
Qed.

Lemma exactlyn1_len:
  forall L : coins, exactlyn 1 L -> length L > 0.
Proof.
  intros L H.
  apply exactlyn_len in H.
  lia.
Qed.

Lemma procSplit_lt_gt:
  forall p:proc, forall L1 L2 L3 : coins,
    procWorks p -> 
    procDepth p = length L1 -> 
    exactlyn 1 L1 ->
    hd gold (procEval p ((L1 ++ L2) ++ L3)) = fake.
Proof.
  intros p L1 L2 L3 Hp Hdepth Hexact.

  assert (Hduh: procDepth p <= length (L1 ++ L2)).
  rewrite Hdepth.
  rewrite app_length.
  lia.

  rewrite (procDepth_tl p (L1 ++ L2) L3 Hduh).
  assert (Hlen4: length (procEval p (L1 ++ L2)) > 0).
  apply exactlyn1_len in Hexact.
  rewrite<- (procEval_length p (L1 ++ L2)).
  rewrite app_length.
  lia.

  rewrite (hd_app _ _ _ _ Hlen4).
  
  assert (Hlen5: length (procEval p L1) > 0).
  apply exactlyn1_len in Hexact.
  rewrite<- (procEval_length p L1).
  lia.
  
  assert (Hduh2: procDepth p <= length L1).
  lia.

  rewrite (procDepth_tl p L1 L2 Hduh2).

  rewrite (hd_app _ _ _ _ Hlen5).
  apply Hp.
  lia.
  exact Hexact.
Qed.

Lemma procSplit_works: 
  forall pdw pdrest :proc,
    (procWorks pdw) -> 
    (procWorks pdrest) ->
    (procWorks (procSplit pdw pdrest)).
Proof.
  intros pdw pdrest Hdw Hdrest.
  unfold procWorks.
  intros L Hlen Hexact.
  rewrite procSplit_depth in Hlen.
  unfold procSplit.
  unfold procEval.
  fold procEval.
  set (dw := procDepth pdw).
  set (drest := procDepth pdrest).
  assert (HL := (list_split _ L (dw + dw) drest Hlen)).
  destruct HL as [Lx].
  destruct H as [L3].
  decompose [and] H.
  clear H.
  assert (HL2 := (list_split _ Lx dw dw H0)).
  destruct HL2 as [L1].
  destruct H as [L2].
  decompose [and] H.
  clear H.
  rewrite H6 in H3.
  rewrite H3 in *.
  rewrite<- H1 at 1.
  rewrite<- H5 in H1.
  assert (Hw := (weigh_exactlyn L1 L2 L3 H1 Hexact)).


  remember (weigh (length L1) ((L1 ++ L2) ++ L3)) as ww.
  destruct ww.

  (* case Eq *)
  rewrite<- H6.
  rewrite<- H0.
  rewrite<- H2.
  rewrite (swap_app _ Lx L3).
  
  assert (Hduh: procDepth pdrest <= length L3).
  fold drest.
  lia.
  rewrite (procDepth_tl pdrest L3 Lx Hduh).
  assert (Hlen3 : length (procEval pdrest L3) > 0).
  apply exactlyn1_len in Hw.
  rewrite<- (procEval_length pdrest L3).
  lia.
  rewrite (hd_app _ _ Lx _ Hlen3).
  apply Hdrest.
  fold drest.
  exact H2.
  exact Hw.
  
  (* case Lt *)
  apply procSplit_lt_gt.
  auto.
  fold dw; rewrite<- H5; rewrite <- H1.
  reflexivity.
  exact Hw.

  (* case Gt *)
  assert (Hlen1 : dw + dw <= length (L1 ++ L2)).
  rewrite H6 in H0.
  rewrite H0.
  lia.

  rewrite (swap_tl _ (L1 ++ L2) L3 _ _ Hlen1).
  
  rewrite<- H5.
  rewrite<- H1 at 1.
  rewrite (swap_app _ L1 L2).

  apply procSplit_lt_gt.
  exact Hdw.
  fold dw.
  rewrite H5.
  reflexivity.

  exact Hw.
Qed.
                                                               
Function pn (n:nat) {measure (fun x => n ) n } :=
  match n with
    | 0 => Stop
    | 1 => (Swap 0 1 Stop)  (* This hack makes the procDepth uniform. *)
(*     | 2 => (Weigh 1 Stop Stop (Swap 1 1 Stop)) *)
    | k => 
      (let d := k/3 in
       match k mod 3 with
         | 2 =>  procSplit (pn (d+1)) (pn d)
         | m =>  procSplit (pn d) (pn (d+m))
       end)
  end.
Proof.
  (* case *)
  intros n n0 n1 Hn0 Hn Hn1.
  rewrite<- Hn.
  apply mul_div_mod_lt.
  lia.
  destruct n1.
  simpl in Hn1.
  lia.
  lia.
  lia.
  
  (* case *)
  intros n n0 n1 Hn0 Hn Hn1.
  rewrite<- Hn.
  rewrite<- (plus_0_r (n/3)).
  apply mul_div_mod_lt.
  lia.
  destruct n1.
  simpl in Hn1.
  lia.
  lia.
  lia.
  
  (* case *)
  intros n n0 n1 Hn0 Hn n2 Hn2 Hn1.
  apply mul_div_mod_lt.
  lia.
  destruct n1.
  simpl in Hn1.
  lia.
  lia.
  lia.
  
  (* case *)
  intros n n0 n1 Hn0 Hn n2 Hn2 Hn1.
  rewrite<- Hn.
  rewrite<- (plus_0_r (n/3)).
  apply mul_div_mod_lt.
  lia.
  destruct n1.
  simpl in Hn1.
  lia.
  lia.
  lia.
  
  (* case *)
  intros n n0 n1 Hn0 Hn n2 n3 Hn3 Hn2 Hn1.
  rewrite<- Hn.
  rewrite<- (plus_0_r (n/3)).
  destruct n1.
  rewrite Hn.
  simpl.
  lia.
  apply mul_div_mod_lt.
  lia.
  lia.
  lia.
  
  (* case *)
  intros n n0 n1 Hn0 Hn n2 n3 Hn3 Hn2 Hn1.
  destruct n1.
  simpl.
  lia.
  apply mul_div_mod_lt.
  lia.
  lia.
  lia.
  
  (* case *)
  intros n n0 n1 Hn0 Hn n2 n3 n4 Hn3 Hn2 Hn1.
  destruct n1.
  simpl in Hn1.
  lia.
  apply mul_div_mod_lt.
  lia.
  lia.
  lia.
  
  (* case *)
  intros n n0 n1 Hn0 Hn n2 n3 n4 Hn3 Hn2 Hn1.
  destruct n1.
  simpl in Hn1.
  lia.
  rewrite<- Hn.
  rewrite<- (plus_0_r (n/3)).
  apply mul_div_mod_lt.
  lia.
  lia.
  lia.
Defined.

Lemma pn_depth:
  forall n:nat, procDepth (pn n) = n.
Proof.
  intros n.

  functional induction (pn n).
  simpl; lia.
  simpl; lia.
  
  assert (Hez :  n / 3 + 1 + (n / 3 + 1) + n / 3 = 3 * (n/3) + 2).
  lia.
  
  rewrite procSplit_depth.
  rewrite IHp.
  rewrite IHp0.
  rewrite Hez.
  rewrite<- e0 at 3.
  symmetry.
  apply Nat.div_mod.
  lia.
  
  rewrite procSplit_depth.
  rewrite IHp.
  rewrite IHp0.
  
  assert (Hez :  n / 3 + n / 3 + (n / 3 + n mod 3) = 3 * (n/3) + n mod 3).
  lia.
  rewrite Hez.
  rewrite<- Nat.div_mod.
  auto.
  auto.
Qed.

Lemma pnWorks:
  forall n:nat, procWorks (pn n).
Proof.
  intro n.
  functional induction (pn n).

  (* Case 0 *)
  unfold procWorks.
  simpl.
  intros L Hlen Hexact.
  apply exactlyn1_len in Hexact.
  lia.

  (* Case 1 *)
  unfold procWorks.
  simpl.
  intros L Hlen Hexact.
  inversion Hexact.
  simpl.
  auto.

  rewrite<- H1 in Hlen.
  simpl in Hlen.
  apply eq_add_S in Hlen.
  apply exactlyn1_len in H.
  lia.


  (* Case n/3 mod 3 = 2 *)
  apply procSplit_works.
  exact IHp.
  exact IHp0.

  (* Case n/3 mod 3 <> 2 *)
  apply procSplit_works.
  exact IHp.
  exact IHp0.
Qed.

Lemma pn_cost_monotonic_S: 
  forall n : nat, procCost (pn n) <= procCost (pn (S n)).
Proof.
  intro n.

  functional induction (pn n).

  (* Case n = 0 *)
  simpl. lia.

  (* Case n = 1 *)
  simpl. lia.

  (* Case n mod 3 = 2 *)
  unfold procSplit.
  unfold procCost. fold procCost.
  remember (procCost (pn (n/3 + 1))) as c31.
  remember (procCost (pn (n/3))) as c30.
  
  rewrite pn_equation.

  assert (Hsilly: S n mod 3 = 0).
  replace (S n) with (n + 1).
  rewrite Nat.add_mod.
  rewrite e0.
  simpl.
  auto.
  auto.
  lia.
  rewrite Hsilly.
  destruct n.
  simpl in e0.
  lia.
  
  unfold procSplit.
  unfold procCost. fold procCost.

  rewrite plus_0_r.
  rewrite Max.max_idempotent.
  rewrite Max.max_idempotent.

  apply plus_le_compat_l.

  assert (Hsilly2: S (S n) / 3 = (S n) / 3 + 1).
  apply mod_div_step.
  auto.
  exact Hsilly.

  rewrite<- Hsilly2 in Heqc31.
  rewrite<- Heqc31.

  apply Max.max_lub.
  auto.
  apply Max.max_lub.
 
  rewrite<- Nat.add_1_r in IHp0.
  rewrite<- Hsilly2 in IHp0.
  rewrite<- Heqc31 in IHp0.
  exact IHp0.

  auto.

  (* Case n mod 3 <> 2 *)
  unfold procSplit.
  unfold procCost. fold procCost.

  remember (procCost (pn (n / 3 + n mod 3))) as cnm3.
  remember (procCost (pn (n/3))) as cn3.

  rewrite pn_equation.

  destruct n.
  contradiction y.

  remember (S (S n) mod 3) as m3.
  
  assert (Hm3 : m3 = 0 \/ m3 = 1 \/ m3 = 2).
  assert (H' : (S (S n) mod 3) < 3).
  apply Nat.mod_bound_pos.
  lia.
  lia.
  lia.

  decompose [or] Hm3.
  
  assert (H2 : S n mod 3 = 2).
  rewrite<- (Nat.mod_small 2 3) at 2.
  rewrite (mod_plus_compat _ _ 3 1).
  simpl ((2+1) mod 3).
  rewrite Nat.add_1_r.
  rewrite<- Heqm3.
  exact H.
  auto.
  auto.
  rewrite H2 in y0.
  contradiction y0.

  rewrite H0.
  assert (H1: S n mod 3 = 0).
  rewrite<- (Nat.mod_same 3) at 2.
  rewrite (mod_plus_compat _ _ 3 1).
  rewrite Nat.add_1_r.
  rewrite<- Heqm3.
  rewrite H0.
  simpl.
  reflexivity.
  auto.
  auto.

  rewrite H1 in *.
  
  assert(H2 : S (S n) / 3 = (S n) / 3).
  apply mod_div_nostep.
  lia.
  rewrite<- Heqm3.
  rewrite H0.
  auto.
  rewrite H2.

  unfold procSplit; unfold procCost; fold procCost.

  rewrite<- Heqcn3.
  
  apply plus_le_compat_l.
  apply Nat.max_le_compat_l.
  apply Nat.max_le_compat_r.
  
  rewrite plus_0_r in IHp0.
  rewrite<- Nat.add_1_r in IHp0.

  exact IHp0.

  rewrite H0.
  unfold procSplit; unfold procCost; fold procCost.

  apply plus_le_compat_l.

  assert (H2 : S (S n) / 3 = (S n) / 3).
  apply mod_div_nostep.
  lia.
  rewrite<- Heqm3; rewrite H0.
  auto.
  rewrite H2.
  
  rewrite<- Heqcn3.

  assert (Hm : (S n) mod 3 = 1).
  rewrite<- (Nat.mod_1_l 3) at 2.
  apply<- (mod_plus_compat (S n) 1 3 1).
  rewrite Nat.add_1_r.
  rewrite<- Heqm3.
  simpl.
  exact H0.
  auto.
  auto.

  rewrite Hm in Heqcnm3.
  rewrite<- Heqcnm3.

  rewrite (Max.max_assoc _ cn3 _).
  rewrite (Max.max_comm _ cn3).
  rewrite<- (Max.max_assoc _ cnm3 _).
  rewrite Max.max_idempotent.
  rewrite (Max.max_assoc cn3 cn3 _).
  rewrite Max.max_idempotent.
  lia.
Qed.

Lemma pn_cost_monotonic_add:
  forall n k:nat, procCost (pn n) <= procCost (pn (n+k)).
Proof.
  intros n k.
  induction k.
  
  rewrite plus_0_r.
  auto.

  apply (le_trans _ (procCost (pn (n+k))) _).
  exact IHk.
  replace (n+ S k) with (S (n+k)).
  apply pn_cost_monotonic_S.
  lia.
Qed.

Lemma pn_cost_monotonic:
      forall n m:nat, n<=m -> procCost (pn n) <= procCost(pn m).
Proof.
  intros n m Hnm.
  apply Nat.le_exists_sub in Hnm.
  elim Hnm.
  intros k H.
  decompose [and] H.
  rewrite H0.
  rewrite plus_comm.
  apply pn_cost_monotonic_add.
Qed.

Lemma pn_cost_pow3:
  forall n:nat, procCost(pn (3^n)) = n.
Proof.
  intro n. 
  induction n.
  simpl; reflexivity.

  replace (3 ^ (S n)) with (3 * (3 ^ n)).
  remember (3 * 3 ^ n) as k.
  assert (Hduh : 3 ^ n > 0).
  assert (Hyep := Nat.pow_nonzero 3 n).
  lia.
  functional induction (pn k).
  lia.
  lia.

  rewrite mult_comm in e0.
  rewrite Nat.mod_mul in e0.
  lia.
  auto.
  
  rewrite (mult_comm 3 _).
  rewrite Nat.mod_mul.
  rewrite Nat.div_mul.
  rewrite plus_0_r.
  
  unfold procSplit; unfold procCost; fold procCost.

  rewrite IHn.
  rewrite Max.max_idempotent.
  rewrite Max.max_idempotent.
  lia.
  auto.
  auto.

  symmetry.
  apply Nat.pow_succ_r.
  lia.
Qed.
            
Theorem pn_optimal:
  forall p:proc, procWorks p -> procCost (pn (procDepth p)) <= procCost p.
Proof.
  intros p Hp.
  apply proc_bound in Hp.
  apply (le_trans _ (procCost (pn (3 ^ (procCost p)))) _).
  apply pn_cost_monotonic.
  exact Hp.

  rewrite pn_cost_pow3.
  auto.
Qed.

(** Ta-daaaa *)


End Scales.

(* Local Variables: *)
(* coq-prog-name: "/usr/local/bin/coqtop" *)
(* coq-load-path: ("/Users/Fred/Documents/proofs/scales") *)
(* End: *)
