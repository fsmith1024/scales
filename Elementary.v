(** * Elementary 

   This module contains basic facts about lists and numbers that
   aren't part of the standard library.

 *)

Require Import Bool.
Require Import Arith.
Require Import List.
Require Import ListSet.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Psatz.
Require Import Permutation.

Import ListNotations.

Ltac smash := 
  repeat 
    (auto;simpl;
     match goal with
       | [ H : ?P |- ?P ] => (exact H)
       | [ H : forall x:nat, _ -> _, _:nat |- _] => apply H
       | [ |- forall x:_, _ ] => intro x
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
       | [ |- context [(nat_compare ?X1 ?X1)] ] =>
         (let H := fresh "H" in
          assert (H: X1 = X1) by reflexivity;
          apply nat_compare_eq_iff in H;
          rewrite H)
     end); 
  auto.

(** ** Nat *)
Lemma plus_reg_r:
  forall n m p : nat, n + p = m + p -> n = m.
Proof.
  intros n m p H.
  apply (plus_reg_l n m p).
  rewrite (plus_comm p n).
  rewrite (plus_comm p m).
  exact H.
Qed.


Lemma nat_compare_plus:
  forall a n m:nat, nat_compare (a+n) (a+m) = nat_compare n m.
Proof.
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

Hint Resolve nat_compare_plus.

Definition flip x :=
  match x with
    | Gt => Lt
    | Lt => Gt
    | Eq => Eq
  end.

Lemma nat_compare_flip:
  forall n m:nat, nat_compare n m = flip (nat_compare m n).
Proof.
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
Proof.
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

Hint Rewrite nat_compare_0_minus.

Lemma nat_compare_minus_0:
  forall m n:nat, n<=m -> nat_compare (m - n) 0 = nat_compare m n.
Proof.
  intros m n.
  rewrite nat_compare_flip.
  rewrite (nat_compare_flip m n).
  intro Hlen.
  apply f_equal.
  apply nat_compare_0_minus.
  exact Hlen.
Qed.

Hint Rewrite nat_compare_minus_0.

Lemma nat_le0:
  forall n:nat, 0 >= n -> n = 0.
Proof.
  intros n Hn.
  lia.
Qed.

Hint Resolve nat_le0.

Lemma nat_compare_minus:
  forall a n m:nat, a>=n -> a>=m -> nat_compare (a-n) (a-m) = nat_compare m n.
Proof.
  intro a.
  induction a.
  smash.
  intro H.
  apply nat_le0 in x.
  apply nat_le0 in H.
  smash.

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
  smash.
Qed.

Lemma max_lub_4:
  forall a b c d m : nat,
    max a (max (max b c) d) <= m -> a <= m /\ b <= m /\ c <= m /\ d <= m.
Proof.
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

Lemma max_eq_r:
  forall n m p:nat,
    n<=p -> m=p -> (Peano.max n m = p).
Proof.
  intros n m p Hnm Hmp.
  rewrite Hmp.
  apply Max.max_r.
  exact Hnm.
Qed.

Lemma max_eq_l:
  forall n m p:nat,
    m <= p -> n = p -> (Peano.max n m = p).
Proof.
  intros n m p Hnm Hnp.
  rewrite<- Hnp.
  lia.
Qed.

Lemma max_plus:
  forall n m: nat,
    Peano.max (n+m) n = (n+m).
Proof.
  intros n m.
  rewrite (plus_n_O n) at 2.
  rewrite Max.plus_max_distr_l.
  rewrite Max.max_0_r.
  reflexivity.
Qed.

Lemma pow_max: 
  forall a n m:nat, 
    a<>0 -> a ^ (max n m) = (max (a ^ n) (a ^ m)).
Proof.
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

Lemma mul_div_mod_lt:
  forall n z k,
    z>1 -> n >= z -> k <= n mod z -> (n/z + k) < n.
Proof.
  intros n z k Hz Hn Hk.
  assert (H1 : n/z + k <= n/z + n mod z).
  lia.
  apply (le_lt_trans _ (n/z + n mod z)).
  exact H1.
  apply (lt_le_trans _ ((z-1)*(n/z) + (n/z + n mod z)) _).
  apply Nat.lt_add_pos_l.
  apply Nat.mul_pos_pos.
  lia.
  apply Nat.div_str_pos.
  lia.
  
  rewrite plus_assoc.
  rewrite<- mult_succ_l.
  rewrite<- Nat.add_1_r.
  rewrite Nat.sub_add.
  rewrite<- Nat.div_mod.
  lia.
  lia.
  lia.
Qed.

Lemma plus_eq_self_r:
  forall m n:nat, n + m = m -> n = 0.
Proof.
  intros m n H.
  lia.
Qed.

Lemma mod_div_nostep:
  forall a b : nat,
    b<>0 -> (S a) mod b > 0 -> (((S a) / b) = a/b).
Proof.
  intros a b Hb Hmod.
  rewrite (Nat.div_mod a b Hb) at 1.
  rewrite<- Nat.add_1_r.
  rewrite<- plus_assoc.
  rewrite mult_comm at 1.
  rewrite (Nat.div_add_l _ _ _ Hb).
  rewrite<- (plus_0_r (a / b)) at 2.
  apply Nat.add_cancel_l.
  apply Nat.div_small.
  assert(H: a mod b < (b-1) \/ a mod b = b-1).
  assert (H2 := Nat.mod_upper_bound a b Hb).
  lia.
  destruct H as [Hlt | Heq].
  lia.
  
  assert (Hbgt1: b > 1).
  destruct b.
  lia.
  destruct b.
  simpl in Hmod.
  lia.
  lia.
  
  rewrite<- Nat.add_1_r in Hmod.
  rewrite (Nat.add_mod _ _ _ Hb) in Hmod.
  rewrite Heq in Hmod.
  rewrite (Nat.mod_1_l _ Hbgt1) in Hmod.
  replace (b - 1 + 1) with b in Hmod.
  
  rewrite Nat.mod_same in Hmod.
  lia.
  exact Hb.
  lia.
Qed.

Lemma mod_div_step:
  forall a b:nat,
    b<>0 -> (S a) mod b = 0 -> ((S a)/b = a/b + 1).
Proof.
  intros a b Hb Hmod.
  
  assert (Hmod' := Hmod).
  
  assert(Hcases: b = 1 \/ b>1).
  lia.
  destruct Hcases as [H1 | Hgt1].
  rewrite H1.
  rewrite Nat.div_1_r.
  rewrite Nat.div_1_r.
  lia.
  
  rewrite<- Nat.add_1_r in Hmod.
  rewrite Nat.add_mod in Hmod.
  rewrite (Nat.mod_1_l b Hgt1) in Hmod.
  
  assert (Hbound : a mod b + 1 < b +1).
  apply plus_lt_compat_r.
  apply Nat.mod_bound_pos.
  lia.
  lia.
  
  assert (Hcases: a mod b + 1 = b \/ a mod b + 1 < b).
  lia.
  
  destruct Hcases as [Htrue | Hbogus].
  
  apply (Nat.mul_cancel_l _ _ b Hb).
  rewrite mult_plus_distr_l.
  rewrite mult_1_r.
  rewrite<- Htrue at 5.
  rewrite plus_assoc.
  rewrite<- (Nat.div_mod _ b Hb).
  rewrite (plus_n_O (b * (S a / b))).
  rewrite<- Hmod' at 1.
  rewrite<- (Nat.div_mod _ b Hb).
  lia.
  
  rewrite (Nat.mod_small _ _ Hbogus) in Hmod.
  lia.
  lia.
Qed.

Lemma mod_plus_compat:
  forall a b n d : nat,
    n <> 0 -> ((a mod n = b mod n) <-> ((a + d) mod n = (b + d) mod n)).
Proof.
  intros a b n d Hn.
  apply conj.
  
  intros H.
  rewrite<- (Nat.add_mod_idemp_l _ _ _ Hn) at 1.
  rewrite H.
  rewrite (Nat.add_mod_idemp_l _ _ _ Hn) at 1.
  reflexivity.
  
  intros H.
  induction d.
  rewrite plus_0_r in H.
  rewrite plus_0_r in H.
  exact H.
  
  apply IHd.
  clear IHd.
  
  replace (a + S d) with ((a+d) + 1) in H.
  replace (b + S d) with ((b+d) + 1) in H.
  
  rewrite<- (Nat.add_mod_idemp_l (a+d) 1 n Hn) in H. 
  rewrite<- (Nat.add_mod_idemp_l (b+d) 1 n Hn) in H.
  
  assert (Had : (a + d) mod n + 1 < n \/ (a+d) mod n + 1 = n).
  apply le_lt_or_eq.
  assert (H' := (Nat.mod_upper_bound (a + d) n Hn)).
  lia.
  
  assert (Hbd : (b + d) mod n + 1 < n \/ (b+d) mod n + 1 = n).
  apply le_lt_or_eq.
  assert (H' := (Nat.mod_upper_bound (b + d) n Hn)).
  lia.
  
  remember ((b + d) mod n) as bd.
  remember ((a + d) mod n) as ad.
  
  destruct Had as [Hads | Hadn].
  destruct Hbd as [Hbds | Hbdn].
  
  rewrite (Nat.mod_small (ad + 1) n Hads) in H.
  rewrite (Nat.mod_small (bd + 1) n Hbds) in H.
  lia.
  
  rewrite (Nat.mod_small (ad + 1) n Hads) in H.
  rewrite Hbdn in H.
  rewrite (Nat.mod_same n Hn) in  H.
  lia.
  
  destruct Hbd as [ Hbds | Hbdn ].
  rewrite Hadn in H.
  rewrite (Nat.mod_same n Hn) in H.
  
  rewrite (Nat.mod_small (bd + 1) n Hbds) in H.
  lia.
  
  lia.
  lia.
  lia.
Qed.

(** ** Lists *)

(** *** Length *)
Lemma firstn_length_app:
  forall A:Type, forall L1 L2 : (list A), (firstn (length L1) (L1 ++ L2)) = L1.
Proof.
  smash.
  induction L1.
  smash.
  smash.
Qed.

Hint Rewrite <- firstn_length_app.

Lemma hd_length:
  forall A:Type, forall L1 L2 L3 L4 : list A,
    length L1 = length L2 -> (L1 ++ L3 = L2 ++ L4) -> L1 = L2.
Proof.
  smash.
  intro H.
  rewrite <- (firstn_length_app A L1 L3).
  rewrite <- (firstn_length_app A L2 L4).
  smash.
Qed.

Hint Resolve hd_length.

Lemma tail_length: 
  forall A:Type, forall L1 L2 L3 L4 : list A, 
    length L1 = length L2 -> L1 ++ L3 = L2 ++ L4 -> L3 = L4.
Proof.
  smash.
  intro H.
  assert(H2 : L1 = L2).
  eapply hd_length.
  exact x.
  exact H.
  rewrite H2 in H.
  smash. 
  apply (app_inv_head L2).
  smash.
Qed.

Hint Resolve tail_length.

Lemma length_app_eq_first:
  forall A:Type, forall L1 L2 L3 L4 : list A,
    L1 ++ L3 = L2 ++ L4 -> (length L3 = length L4) -> (length L1 = length L2).
Proof.
  smash.
  intro H.
  apply (plus_reg_r _ _ (length L3)).
  rewrite H at 2.
  rewrite<- app_length.
  rewrite<- app_length.
  rewrite x.
  reflexivity.
Qed.

Lemma length_app_eq_second:
  forall A:Type, forall L1 L2 L3 L4 : list A,
    L1 ++ L3 = L2 ++ L4 -> (length L1 = length L2) -> (length L3 = length L4).
Proof.
  smash.
  intro H.
  apply (plus_reg_l _ _ (length L1)).
  rewrite H at 2.
  rewrite<- app_length.
  rewrite<- app_length.
  rewrite x.
  reflexivity.
Qed.

Lemma length_app_eq_fst:
  forall A:Type, forall L1 L2 L3 L4 : list A,
    L1 ++ L3 = L2 ++ L4 
    -> (length L1 = length L2 \/ length L3 = length L4) 
    -> L1 = L2.
Proof.
  smash.
  intro Hor; decompose [or] Hor.
  apply (hd_length _ L1 L2 L3 L4 H x).
  assert (Hlen: length L1 = length L2).
  rewrite<- (Nat.add_cancel_r _ _ (length L4)).
  rewrite<- H at 1.
  rewrite<- app_length.
  rewrite<- app_length.
  rewrite x.
  reflexivity.
  apply (hd_length _ L1 L2 L3 L4 Hlen x).
Qed.

Hint Resolve length_app_eq_fst.

Lemma length_app_eq_snd:
  forall A:Type, forall L1 L2 L3 L4 : list A,
    L1 ++ L3 = L2 ++ L4 
    -> (length L1 = length L2 \/ length L3 = length L4) 
    -> L3 = L4.
Proof.
  smash.
  intro H.
  apply length_app_eq_fst in H.
  assert (Hlen: length L1 = length L2).
  rewrite H.
  reflexivity.
  apply (tail_length A L1 L2 L3 L4 Hlen x).
  exact x.
Qed.

Hint Resolve length_app_eq_snd.

Lemma skipn_length:
  forall A:Type, forall L : (list A), forall n:nat, length(skipn n L) = (length L) - n.
Proof.
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

Lemma skipn_app: 
  forall A:Type, forall L1 L2 : list A,
    (skipn (length L1) (L1 ++ L2)) = L2.
Proof.
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
Proof.
  intros A L.
  induction L.
  simpl.
  reflexivity.
  simpl.
  f_equal.
  apply IHL.
Qed.

Lemma list_length0:
  forall A:Type, forall L: list A, length L = 0 -> L = [].
Proof.
  intros A L.
  induction L.
  smash.
  smash.
  discriminate.
Qed.

Hint Resolve list_length0.

Lemma length_nil_S:
  forall A:Type, forall n:nat, length ([]:list A) = S n -> False.
Proof.
  intros A N H.
  simpl in H.
  symmetry in H.
  apply NPeano.Nat.neq_succ_0 in H.
  exact H.
Qed.

Lemma length_cons: 
  forall A:Type, forall L:list A, forall n:nat,
    (length L) = (S n) -> exists a:A, exists L1: list A, L = (a::L1).
Proof.
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
Proof.
  intros A L1 L2 a.
  rewrite app_length.
  rewrite app_length.
  simpl.
  rewrite plus_n_Sm.  
  reflexivity.
Qed.

(** *** App *)

Lemma app_cons_ignore:
  forall A:Type, forall L11 L12 L21  L22 : (list A), forall a : A,
    (length L11 = length L21)
    -> (L11 ++ L12 = L21 ++ L22)
    -> (L11 ++ (a::L12) = L21 ++ (a::L22)).
Proof.
  smash.
  intro H.
  smash.
  apply (length_app_eq_fst _ L11 L21 L12 L22 H).
  left; exact x.
  apply (length_app_eq_snd _ L11 L21 L12 L22 H).
  left; exact x.
Qed.

Hint Resolve app_cons_ignore.

Lemma breakup:
  forall n m k,
    n = (m+k)
    -> forall A:Type, forall Ln : list A, 
         (length Ln) = n
         -> exists Lm Lk : list A, (Ln = Lm ++ Lk) /\
                                   (length Lm = m) /\
                                   (length Lk = k).
Proof.
  intro n.
  induction n.
  smash.
  intros Hlen.
  exists [].
  exists [].
  simpl.
  apply conj.
  auto.
  lia.

  smash.
  destruct Ln.
  simpl.
  discriminate.
  simpl.
  intro Hlen.

  destruct m.
  apply eq_add_S in Hlen.
  
  assert (Hn0 : n = 0 + n) by lia.
  assert (Hn := (IHn 0 n Hn0 A Ln Hlen)).
  destruct Hn as [ Lm Hn].
  destruct Hn as [ Lk Hn].
  exists Lm.
  exists (a::Lk).
  simpl.
  decompose [and] Hn.
  apply list_length0 in H1.
  subst Lm.
  simpl.
  rewrite H.
  simpl.
  apply conj.
  auto.
  apply conj.
  auto.
  rewrite H2.
  smash.

  assert (Hnmk : n = m + k) by lia.
  apply eq_add_S in Hlen.
  assert (Hn := IHn m k Hnmk A Ln Hlen).
  destruct Hn as [ Lm Hn].
  destruct Hn as [ Lk Hn].
  exists (a::Lm).
  exists Lk.
  decompose [and] Hn.
  apply conj.
  smash.
  apply conj.
  smash.
  smash.
Qed.

Lemma list_split: 
  forall A:Type, 
  forall L: list A,
  forall n1 n2:nat,
    length L = n1 + n2 ->
    exists L1 L2 : list A,
      length L1 = n1 /\ length L2 = n2 /\ L = L1 ++ L2.
Proof.
  intros A L n1 n2 Hlen.
  exists (firstn n1 L).
  exists (skipn n1 L).
  apply conj.
  rewrite List.firstn_length.
  rewrite Hlen.
  lia.
  apply conj.
  rewrite skipn_length.
  rewrite Hlen.
  lia.
  rewrite (firstn_skipn n1).
  reflexivity.
Qed.

Lemma hd_app:
  forall A:Type, forall L1 L2: list A, forall a : A, 
    length L1 > 0 -> hd a (L1 ++ L2) = hd a L1.
Proof.
  intros A L1 L2 a Hlen.
  destruct L1.
  simpl in Hlen.
  apply gt_irrefl in Hlen.
  contradiction.
  simpl.
  reflexivity.
Qed.

Lemma app_eq_nil_rev: 
  forall A:Type,
  forall L1 L2 : list A,
    L1 = [] -> L2 = [] -> (L1 ++ L2 = []).
Proof.
  intros A L1 L2 H1 H2.
  rewrite H1.
  rewrite H2.
  simpl.
  reflexivity.
Qed.

(** *** Filter, NoDup, and In *)

Lemma in_filter_app3: 
  forall A:Type, forall f1 f2 f3: A -> bool, forall L1 L2 L3: list A, forall a:A,
    In a ((filter f1 L1) ++ (filter f2 L2) ++ (filter f3 L3)) <->
    (In a L1 /\ (f1 a = true)) \/ 
    (In a L2 /\ (f2 a = true)) \/ 
    (In a L3 /\ (f3 a = true)).
Proof.
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

Lemma filter_length: 
  forall A:Type, forall f: A -> bool, forall L : list A,
    length (filter f L) <= length L.
Proof.
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

(* Prove a basic prooperty of NoDup and map. *)
Lemma NoDup_map: 
  forall A B:Type, forall f:A -> B, forall L:list A,
    (forall a1 a2 : A, In a1 L -> In a2 L -> (f a1) = (f a2) -> a1 = a2)
    -> NoDup L
    -> NoDup (map f L).
Proof.
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
Proof.
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
Proof.
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
  forall A : Type,
  forall f : A -> bool,
  forall L1 L2 : list A,
    NoDup L1 -> NoDup L2  -> (filter f L2 = nil) -> NoDup ((filter f L1) ++ L2).
Proof.
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
  forall A:Type,
  forall f : A -> bool,
  forall L1 L2: list A,
    (filter f (L1 ++ L2)) = (filter f L1) ++ (filter f L2).
Proof.
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
  forall A:Type,
  forall f1 f2: A -> bool,
  forall L: list A, 
    (filter f1 (filter f2 L)) = (filter (fun x => (f1 x) && (f2 x)) L).
Proof.
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
  forall A:Type,
  forall f1 f2: A -> bool,
    (forall x:A, ((f1 x)=true -> (f2 x)=false) /\ ((f2 x)=true -> (f1 x)=false))
    -> forall L:list A, (filter f1 (filter f2 L)) = [].
Proof.
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

Lemma In_split:
  forall A:Type, forall L1 L2:list A, forall b: A,
    In b (L1 ++ L2) -> (forall a:A, In b (L1 ++ (a::L2))).
Proof.
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
Proof.
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

Lemma In_one: 
  forall A:Type, forall a b:A, 
    In a (b::nil) <-> b = a.
Proof.
  intros A a b.
  apply conj.
  intro H.
  unfold In in H.
  decompose [or] H.
  exact H0.
  contradiction.
  intro H.
  rewrite H.
  apply in_eq.
Qed.


Lemma NoDup_cons_inv:
  forall A:Type, forall L:list A, forall a:A,
    NoDup (a::L) -> NoDup L.
Proof.
  intros A L a H.
  inversion H.
  exact H3.
Qed.

Lemma NoDup_remove_cons:
  forall A:Type, forall L: list A, forall a : A,
    NoDup (a::L) -> ~ (In a L).
Proof.
  intros A L a H.
  replace (a::L) with ([] ++ (a::L)) in H.
  apply NoDup_remove_2 in H.
  simpl in H.
  exact H.
  simpl; reflexivity.
Qed.



(* Local Variables: *)
(* coq-prog-name: "/usr/local/bin/coqtop" *)
(* coq-load-path: ("/Users/Fred/Documents/proofs/scales") *)
(* End: *)
