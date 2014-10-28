Require Import NZAxioms NZMulOrder NZPow NZDomain.
Require Import Psatz.

Module Type Log (Import A: Typ).
  Parameter Inline log : t -> t -> t.
End Log.

Module Type NLogSpec (A: NZOrdAxiomsSig') (B: Pow' A) (C: Log A).
  Import A B C.

  Axiom log_spec: forall n a, n > 1 -> 0 < a -> n^(log n a) <= a < n^(S (log n a)).
  Axiom log_nonpos: forall n a, n>1 -> a<=0 -> log n a == 0.

End NLogSpec.

Module Type NLog (A : NZOrdAxiomsSig) (B : Pow A) := Log A <+ NLogSpec A B.

Module Type NLogProp 
       (Import A : NZOrdAxiomsSig')
       (Import B : NZPow' A)
       (Import C : NLog A B)
       (Import D : NZMulOrderProp A)
       (Import E : NZPowProp A B D).



Module T := NZDomainProp A.

Section N.

Parameter n : t.

Axiom n_gt1 : n > 1.

Lemma n_gt0 : n > 0.
Proof.
  assert (H:= n_gt1).
  order'.
Qed.

Lemma n_ge0: n >= 0.
Proof.
  assert (H:=n_gt1).
  order'.
Qed.

(** log is always non-negative *)

Lemma log_nonneg : forall a, 0 <= log n a.
Proof.
  intros a. destruct (le_gt_cases a 0) as [Ha|Ha].
  rewrite log_nonpos.
  easy.
  exact n_gt1.
  exact Ha.
  destruct (log_spec n a n_gt1 Ha) as (_,LT).
  apply lt_succ_r, (pow_gt_1 n).
  exact n_gt1.
  rewrite <- le_succ_l, <- one_succ in Ha. 
  order.
Qed.

(** A tactic for proving positivity and non-negativity *)

Ltac order_pos :=
  ((apply add_pos_pos || apply add_nonneg_nonneg ||
          apply mul_pos_pos || apply mul_nonneg_nonneg ||
          apply pow_nonneg || apply pow_pos_nonneg ||
          apply log_nonneg || apply (le_le_succ_r 0));
   order_pos) (* in case of success of an apply, we recurse *)
    || order'.  (* otherwise *)

(** The spec of log indeed determines it *)

Lemma log_unique : forall a b, 0<=b -> n^b<=a<n^(S b) -> log n a == b.
Proof.
  intros a b Hb (LEb,LTb).
  assert (Ha : 0 < a).
  apply lt_le_trans with (n^b); trivial.
  
  apply (pow_pos_nonneg _ _ n_gt0) ; order'.
  assert (Hc := log_nonneg a).
  destruct (log_spec n a n_gt1 Ha) as (LEc,LTc).
  assert (log n a <= b).
  apply lt_succ_r, (pow_lt_mono_r_iff n); try order'.
  exact n_gt1.
  now apply le_le_succ_r.
  assert (b <= log n a).
  apply lt_succ_r, (pow_lt_mono_r_iff n); try order'.
  exact n_gt1.
  now apply le_le_succ_r.
  order.
Qed.

(** Hence log is a morphism. *)

Instance log_wd : Proper (eq==>eq) (log n).
Proof.
  intros x x' Hx.
  destruct (le_gt_cases x 0).
  rewrite (log_nonpos n  x n_gt1 H).
  rewrite (log_nonpos n x' n_gt1).
  trivial.
  
  reflexivity. now rewrite <- Hx.
  apply log_unique. apply log_nonneg.
  rewrite Hx in *.
  now apply (log_spec n x' n_gt1 H).
Qed.

(* ***********{ *)
(* Detour: Subtraction is very underspecified.  Not sure why but it is a major road block. *)

(* 
Known:
  lt_succ_pred: forall z n : t, z < n -> S (P n) == n
  pred_succ:  P (S n) == n
  sub_succ_r: P (n - m) == n - S m
  sub_0_r:    P (n - 0) == n
  sub_wd:     Proper (eq ==> eq ==> eq) sub.
  
lt_ind:
  forall A : t -> Prop,
  Proper (eq ==> iff) A ->
  forall n : t,
  A (S n) ->
  (forall m : t, n < m -> A m -> A (S m)) -> forall m : t, n < m -> A m

central_induction:
  forall A : t -> Prop,
  Proper (eq ==> iff) A ->
  forall z : t, A z -> (forall n : t, A n <-> A (S n)) -> forall n : t, A n

order_induction_0:
  forall A : t -> Prop,
  Proper (eq ==> iff) A ->
  A 0 ->
  (forall n : t, 0 <= n -> A n -> A (S n)) ->
  (forall n : t, n < 0 -> A (S n) -> A n) -> forall n : t, A n
order_induction'_0:
*)

Lemma iter_assoc:
  forall n:nat, forall A : Type, forall f: A -> A, forall a:A,
    f ((nat_iter n f) a) = (nat_iter n f) (f a).
Proof.
  intro n.
  induction n.
  simpl.
  easy.

  intros A f a.
  simpl.
  rewrite IHn.
  easy.
Qed.

Lemma iter_succ_l:
  forall k:nat, forall A:Type, forall f: A -> A, forall a:A,
    f ((nat_iter k f) a) = (nat_iter (Datatypes.S k) f) a.
Proof.
  intros k A f a.
  rewrite iter_assoc.
  symmetry.
  apply nat_iter_succ_r.
Qed.

(* This is a very stupid result basically equivalent to lt_succ_pred. *)
Lemma pred_lt: forall z n : t, z < n -> P n < n.
Proof.
  intros z n Hnz.
  apply succ_lt_mono.
  rewrite (lt_succ_pred _ _ Hnz).
  apply lt_succ_diag_r.
Qed.

Lemma iter_lt: 
  forall k : nat, (0%nat < k)%nat -> forall a : t, (nat_iter k S) a > a.
Proof.
  induction k.
  easy.
  intros H a.
  simpl.
  assert (Hcases:= NPeano.Nat.lt_total 0 k).
  decompose [or] Hcases.
  
  apply lt_lt_succ_r.
  apply IHk.
  exact H0.
  
  rewrite<- H1.
  simpl.
  apply lt_succ_diag_r.
  
  easy.  
Qed.

Lemma iter_le: 
  forall k : nat, forall a : t, a <= (nat_iter k S) a.
Proof.
  intro k.
  induction k.
  simpl.
  easy.

  simpl.
  intro a.
  apply le_le_succ_r.
  apply IHk.
Qed.

Lemma iter_succ_lt: 
  forall a b : t, a < b -> exists k:nat, (nat_iter k S) a == b.
Proof.
  intros a b Hab.
  assert (Hx:= T.itersucc_or_itersucc a b).
  destruct Hx as [k Hx].
  exists k.
  decompose [or] Hx.
  induction k.
  simpl in H.
  order.
  simpl in H.
  assert (Hb := iter_le k b).
  apply le_le_succ_r in Hb.
  symmetry in H.
  rewrite H in Hb.
  apply le_ngt in Hb.
  easy.
  symmetry in H.
  exact H.
Qed.

Lemma iter_succ_le:
  forall a b: t, a<=b -> exists k:nat, (nat_iter k S) a == b.
Proof.
  intros a b H.
  apply lt_eq_cases in H.
  decompose [or] H.
  apply (iter_succ_lt a b H0).
  exists 0%nat.
  simpl.
  exact H0.
Qed.

Lemma iter_sub_succ_r: 
  forall k : nat, forall a b : t,
    b - ((nat_iter k S) a) == (nat_iter k P) (b - a).
Proof.
  intro k.
  induction k.
  intros a b.
  simpl.
  reflexivity.

  intros a b.
  simpl.
  rewrite<- (IHk a b).
  apply sub_succ_r.
Qed.

(* Lemma pred_nat: forall a:t, (forall b:t, a < S b) -> P a == a.
   
   This lemma is unfortunately not true. See NZDomain.v in the
   standard library for an explanation why or read my attempt below..

   Our axiomatization of P requires only that it be surjective, and an
   inverse in the codomain of S which must be injective.
   Unfortunately if S is not surjective (ie, there is an initial
   point), then P can map that initial point to anything.  This is so
   because there is no defined operation on that point.  The only
   constraint on P comes from lt_succ_pred and pred_succ neither of
   which apply for the intial point.  
*)

Inductive pred_safe : nat -> t -> Prop := 
| pred_safe_0 : 
    forall a:t, pred_safe 0%nat a
| pred_safe_S : 
    forall n:nat, forall a:t, 
      P a < a /\ pred_safe n (P a) -> pred_safe (Datatypes.S n) a
.

Lemma pred_safe_succ:
  forall k:nat, forall a:t, pred_safe (Datatypes.S k) a -> pred_safe k a.
Proof.
  intro k; induction k.
  
  intros a Hp.
  apply pred_safe_0.
  
  intros a Hp.
  inversion Hp.
  decompose [and] H0.
  clear H1 H.
  apply pred_safe_S.
  apply conj.
  exact H2.
  apply (IHk _ H3).
Qed.

Instance pred_safe_wd:
  forall k:nat, Proper (eq ==> iff) (pred_safe k).
Proof.
  intro k.
  induction k.

  intros x y Hxy.
  apply conj.
  intro Hy; apply pred_safe_0.
  intro Hy; apply pred_safe_0.

  intros  x y Hxy.
  apply conj.
  intro Hy.
  inversion Hy.
  apply pred_safe_S.
  apply conj.
  decompose [and] H0.
  rewrite<- Hxy.
  exact H2.

  rewrite<- Hxy.
  decompose [and] H0.
  exact H3.

  intro Hy.
  inversion Hy.
  apply pred_safe_S.
  apply conj.
  decompose [and] H0.
  rewrite Hxy.
  exact H2.

  rewrite Hxy.
  decompose [and] H0.
  exact H3.
Qed.

(* I believe the above definition of pred_safe_wd is better than this one. 
Lemma pred_safe_wd:
  forall k:nat, Proper (eq ==> Basics.flip Basics.impl) (pred_safe k).
Proof.
  intro k.
  induction k.

  intros x y Hxy Hy.
  apply pred_safe_0.

  intros  x y Hxy Hy.
  inversion Hy.
  apply pred_safe_S.
  apply conj.
  rewrite Hxy.
  decompose [and] H0.
  exact H2.
  rewrite Hxy.
  decompose [and] H0.
  exact H3.
Qed.
*)

Lemma pred_safe_iter_succ:
  forall k:nat, forall a:t, pred_safe k ((nat_iter k S) a).
Proof.
  intro k.
  induction k.

  intro a.
  apply pred_safe_0.

  intro a.
  apply pred_safe_S.
  simpl.
  
  apply conj.

  rewrite pred_succ.
  apply lt_succ_diag_r.
 
  assert (Hq := pred_safe_wd k).
  rewrite pred_succ.
  exact (IHk a).
Qed.

Lemma pred_safe_plus:
  forall k:nat, forall a:t, 
    pred_safe k a -> 
    forall m:nat, pred_safe (k+m) (nat_iter m S a).
Proof.
  intros k a H m.
  induction m.

  simpl.
  replace (k+0%nat)%nat with k.
  exact H.
  rewrite<- plus_n_O.
  reflexivity.

  replace (k + Datatypes.S m)%nat with (Datatypes.S (k + m)%nat).
  apply pred_safe_S.
  apply conj.
  simpl.
  rewrite pred_succ.
  apply lt_succ_diag_r.
  simpl.
  rewrite pred_succ.
  exact IHm.
  lia.
Qed.

Lemma pred_safe_plus_r:
  forall k m:nat, forall a:t, pred_safe (k + m) a -> pred_safe k a.
Proof.
  intros k m.
  induction m.
  
  replace (k + 0)%nat with k.
  firstorder.
  lia.

  intro a.
  replace (k + Datatypes.S m)%nat with (Datatypes.S (k + m)).
  intro H.
  apply pred_safe_succ in H.
  apply (IHm _ H).
  lia.
Qed.

Lemma lt_succ_cases:
  forall a b:t, a < b -> (S a) == b \/ (S a) < b.
Proof.
  intros a b Hab.
  assert (H := lt_total (S a) b).
  decompose [or] H.
  right; exact H0.
  left; exact H1.
  
  apply nlt_succ_r in Hab.
  apply Hab in H1.
  contradiction.
Qed.

Lemma le_pred_safe:
  forall k:nat, forall a b :t, a <= b -> pred_safe k a -> pred_safe k b.
Proof.

  intros k a b H.

  apply lt_eq_cases in H.
  decompose [or] H.

  apply iter_succ_lt in H0.
  destruct H0 as [ m H0].
  rewrite<- H0.

  intro Hp.
  assert (H2 := pred_safe_plus _ _ Hp m).
  apply (pred_safe_plus_r _ _ _ H2).

  rewrite H0.
  firstorder.
Qed.


Lemma pred_safe_lt: 
  forall k:nat, forall a:t, 
    pred_safe (Datatypes.S k) a -> (nat_iter (Datatypes.S k) P a) < (nat_iter k P a).
 Proof.
   intro k.
   induction k.
   simpl.
   
   intros a Hp.
   inversion Hp.
   decompose [and] H0.
   exact H2.

   intros a Hp.
   inversion Hp.
   decompose [and] H0.
   
   simpl.
   simpl in IHk.
   clear H0 H H1.

   assert (H4 := IHk (P a) H3).
   rewrite iter_assoc.
   exact H4.
Qed.

Lemma succ_pred_safe: 
  forall k:nat, forall a:t, pred_safe k a -> (nat_iter k S) (nat_iter k P a) == a.
Proof.
  intro k.
  induction k.
  
  simpl.
  easy.
  
  intros a Hp.
  simpl.
  rewrite iter_assoc.
  rewrite (lt_succ_pred (P (nat_iter k P a))).
  apply IHk.
  apply (pred_safe_succ _ _ Hp).
  rewrite iter_succ_l.
  apply pred_safe_lt.
  exact Hp.
Qed.

Lemma iter_succ_eq: 
  forall k:nat, forall a b:t, (nat_iter k S) a == (nat_iter k S) b <-> a == b.
Proof.
  intro k.
  induction k.
  simpl.
  easy.

  intros a b.
  simpl.
  apply conj.
  intro H.
  apply IHk.
  apply succ_inj_wd.
  exact H.
  
  intro H.
  apply succ_inj_wd.
  apply IHk.
  exact H.
Qed.

Lemma iter_pred_eq:
  forall k:nat, forall a b:t, 
    pred_safe k a -> pred_safe k b -> (nat_iter k P) a == (nat_iter k P) b -> a == b.
Proof.
  intro k.
  induction k.

  simpl.
  easy.

  intros a b Hap Hbp.
  intro H.
  simpl in H.
  rewrite iter_assoc in H.
  rewrite iter_assoc in H.
  inversion Hap.
  decompose [and] H1.
  inversion Hbp.
  decompose [and] H6.
  clear H0 H2 H5 H7 n1 a1 n0 a0 H1 H6.

  assert (IHs := IHk _ _ H4 H9 H).
  
  apply succ_inj_wd in IHs.
  rewrite (lt_succ_pred (P a) a H3) in IHs.
  rewrite (lt_succ_pred (P b) b H8) in IHs.
  exact IHs.
Qed. 

Lemma pred_safe_exists:
  forall k:nat, forall a b :t,
    a < b -> a == (nat_iter k P) b -> exists m:nat, (a == (nat_iter m P) b /\ pred_safe m b).
Proof.
  intro k.
  induction k.
  intros a b Hab.
  simpl.
  intro H.
  exists 0%nat.
  simpl.
  apply conj.
  exact H.
  apply pred_safe_0.

  intros a b Hab Heq.
  
  simpl in Heq.
  rewrite iter_assoc in Heq.
  assert (Hcases := lt_total a (P b)).
  decompose [or] Hcases.

  assert (IHs := IHk a (P b) H Heq).
  destruct IHs as [ m (Ha,Hp) ].
  exists (Datatypes.S m).
  apply conj.
  simpl.
  rewrite iter_assoc.
  exact Ha.
 
  apply pred_safe_S.
  apply conj.

  apply (pred_lt _ _ Hab).
  exact Hp.

  (* Case a == P b *)
  exists 1%nat.
  simpl.
  apply conj.
  exact H0.
  apply pred_safe_S.
  apply conj.
  rewrite H0 in Hab.
  exact Hab.
  apply pred_safe_0.
  apply succ_lt_mono in H0.
  rewrite (lt_succ_pred _ _ Hab) in H0.
  apply nlt_succ_r in Hab.
  apply Hab in H0.
  contradiction.
Qed.

Lemma lt_plus_0 : forall a b k : t, a < b -> a + k == b -> k > 0.
Proof.
  intros a b k Hab Hak.
  assert (Hcases := lt_total 0 k).
  destruct Hcases.
  exact H.
  destruct H.
  rewrite<- H in Hak.
  rewrite add_0_r in Hak.
  rewrite Hak in Hab.
  apply lt_irrefl in Hab.
  contradiction.
  apply (add_lt_mono_l _ _ a) in H.
  rewrite add_0_r in H.
  rewrite Hak in H.
  apply lt_asymm in H.
  exfalso.
  apply H.
  apply Hab.
Qed.

Lemma pred_inj: forall za zb a b :t, za < a -> zb < b -> P a == P b -> a == b.
Proof.
  intros za zb a b Hza Hzb Hpb.
  assert (Ha := lt_exists_pred za a Hza).  
  assert (Hb := lt_exists_pred zb b Hzb).
  destruct Ha as [ka].
  decompose [and] H.
  clear H.
  destruct Hb as [kb].
  decompose [and] H.
  clear H.
  rewrite H0.
  rewrite H2.
  apply succ_inj_wd.
  rewrite H0 in Hpb.
  rewrite H2 in Hpb.
  rewrite pred_succ in Hpb.
  rewrite pred_succ in Hpb.
  exact Hpb.
Qed.

Lemma iter_pred_succ:
  forall n : nat, forall a:t, (nat_iter n P) ((nat_iter n S) a) == a.
Proof.
  intro n.
  induction n.
  simpl.
  easy.

  intro a.
  simpl.
  rewrite (iter_assoc _ _ P).
  rewrite pred_succ.

  apply IHn.
Qed.

Lemma iter_succ0_or_pred0_safe:
  forall a : t, exists k : nat, 
    a == nat_iter k S 0 \/ (a == nat_iter k P 0 /\ pred_safe k 0).
Proof.
  intro a.

  assert (Hcases := lt_total a 0).
  decompose [or] Hcases.

  assert (Ha := T.itersucc0_or_iterpred0 a).
  destruct Ha as [p Ha].
  decompose [or] Ha.
  exists p.
  left.
  exact H0.

  assert (H2 := pred_safe_exists p a 0 H H0).
  destruct H2 as [m (H2a, H2b)].
  exists m.
  right.
  apply (conj H2a H2b).

  exists 0%nat.
  left.
  simpl.
  exact H0.

  assert (H:= iter_succ_lt _ _ H0).
  destruct H as [k H].
  exists k.
  left.
  symmetry.
  exact H.
Qed.


Lemma sub_diag: forall a : t, 0 <= a -> a - a == 0.
Proof.
  intros a Ha.
  apply iter_succ_le in Ha.
  destruct Ha as [k H].

  rewrite<- H.
  rewrite iter_sub_succ_r.
  rewrite sub_0_r.
  rewrite iter_pred_succ.
  reflexivity.
Qed.

Lemma iter_add_l: 
  forall k:nat, forall a b : t,
    ((nat_iter k S a) + b) == nat_iter k S (a + b).
Proof.
  intro k.
  induction k.
  simpl.
  firstorder.
  
  intros a b.
  simpl.
  rewrite add_succ_l.
  apply succ_inj_wd.
  apply IHk.
Qed.

Lemma sub_le: forall a b k : t, 0 <= a -> a + k == b -> (b - a) == k.
Proof.
  intros a b k H0 Hakb.
  apply iter_succ_le in H0.
  destruct H0 as [m Ha].

  rewrite<- Ha.
  rewrite iter_sub_succ_r.
  rewrite sub_0_r.
  
  rewrite<- Hakb.
  rewrite<- Ha.

  rewrite iter_add_l.
  rewrite iter_pred_succ.
  apply add_0_l.
Qed.

(* The term pred_safe k (b - (nat_iter k P a)) is necessary because
subtraction is under-specified.  The definition of subtraction makes
no requirement on the subtraction of the initial value if it exists
and is less than zero.

This makes the subtraction of negative numbers open to different
interpretations.  I think the following statement is about the
strongest thing one can prove, but the pre-condition means that you
can't use this theorem to find the value of a negative subtraction.
*)

Lemma pred_sub_safe:
  forall k:nat, forall a b : t, pred_safe k a -> pred_safe k (b - (nat_iter k P a)) -> (b - (nat_iter k P a)) == nat_iter k S (b - a).
Proof.
  intros k a b H Hsub.

  rewrite<- (succ_pred_safe _ _ H) at 2.
  rewrite iter_sub_succ_r.
  rewrite (succ_pred_safe _ _ Hsub).
  reflexivity.
Qed.

Lemma sub_succ: 
  forall a b : t, a>=0 -> (S b - S a) ==  (b - a).
Proof.
  intros a b H.
  apply iter_succ_le in H.
  destruct H as [ k H].
  rewrite<- H.
  
  rewrite sub_succ_r.
  rewrite iter_sub_succ_r.
  
  rewrite iter_assoc.
  rewrite sub_0_r.
  rewrite pred_succ.
  
  rewrite iter_sub_succ_r.
  rewrite sub_0_r.
  reflexivity.
Qed.
 
Lemma sub_le_direct: 
  forall a b : t, 0 <= a -> a <= b -> a + (b - a) == b.
Proof.
  intros a b H0 Hab.
  apply le_exists_sub in Hab.
  destruct Hab as [ p (Heq,Hp0)].
  symmetry in Heq.
  rewrite add_comm in Heq.
  assert (Heq2 := (sub_le a b p H0 Heq)).
  rewrite Heq2.
  exact Heq.
Qed.

Lemma sub_succ_l: forall a b:t, 0 <= a -> a <= b -> S b - a == S (b - a).
Proof.
  intros a b Ha Hb.
  apply iter_succ_le in Hb.
  destruct Hb as [kb Hb].

  apply iter_succ_le in Ha.
  destruct Ha as [ka Ha].
  rewrite<- Ha.
  
  rewrite iter_sub_succ_r.
  rewrite sub_0_r.
  rewrite iter_sub_succ_r.
  rewrite sub_0_r.
  
  rewrite<- Ha in Hb.
  rewrite<- nat_iter_plus in Hb.
  rewrite Plus.plus_comm in Hb.
  rewrite nat_iter_plus in Hb.
  rewrite<- Hb.
  rewrite iter_assoc.
  rewrite iter_pred_succ.
  rewrite iter_pred_succ.
  reflexivity.
Qed.

Lemma sub_lt_gt0:
  forall a b : t, 0 <= a -> a < b -> 0 < (b - a).
Proof.
  intros a b Ha Hb.
  assert (Hax := iter_succ_le _ _ Ha).
  destruct Hax as [k Hax].
  assert (Hbx := iter_succ_lt _ _ Hb).
  destruct Hbx as [m Hbx].
  assert (m > 0%nat)%nat.
  destruct m.
  simpl in Hbx.
  rewrite Hbx in Hb.
  apply lt_irrefl in Hb.
  contradiction.
  apply Gt.gt_Sn_O.
  rewrite<- Hax.
  rewrite<- Hbx.
  rewrite iter_sub_succ_r.
  rewrite sub_0_r.
  rewrite<- Hax.
  rewrite<- nat_iter_plus.
  rewrite Plus.plus_comm.
  rewrite nat_iter_plus.
  rewrite iter_pred_succ.
  
  apply iter_lt.
  exact H.
Qed.

Lemma pow_succ_lt:
  forall a b : t, a>1 -> b>=0 -> a^b < a^(S b).
Proof.
  intros a b Ha Hb.
  rewrite pow_succ_r.
  rewrite<- mul_1_l at 1.
  apply mul_lt_mono_pos_r.
  apply pow_pos_nonneg.
  apply (lt_trans _ 1 _).
  rewrite one_succ.
  apply lt_succ_diag_r.
  exact Ha.
  exact Hb.
  exact Ha.
  exact Hb.
Qed.

Lemma log_exists:
    forall a:t,
      a>0 -> exists k m:t, k>=0 /\ (a == n^k + m) /\ m < (n^(S k) - n^k).
Proof.
  apply lt_ind.
  intros x y Hxy.
  apply conj.

  (* This ridiculous pattern is repeated twice. *)
  (* A *)
  intro H.
  destruct H as [k], H as [m].
  exists k, m.
  rewrite<- Hxy.
  exact H.

  (* A *)
  intro H.
  destruct H as [k], H as [m].
  exists k, m.
  rewrite Hxy.
  exact H.

  (* Case a == 0 *)
  exists 0, 0.
  apply conj.
  easy.
  apply conj.
  assert (H0:= pow_0_r n).
  rewrite H0.
  rewrite add_0_r.
  rewrite one_succ.
  easy.

  (* Case a == 0, second clause. *)
  rewrite pow_0_r.
  rewrite pow_succ_r. 
  rewrite pow_0_r.
  rewrite mul_1_r.
  assert (H:=n_gt1).
  rewrite sub_1_r.
  apply succ_lt_mono.
  rewrite (lt_succ_pred 1 n H).
  rewrite<- one_succ.
  exact H.
  easy.
  
  (* Inductive case. *)
  intros m Hm IH.
  destruct IH as [k IH], IH as [m0].
  destruct H as (Hk,(L,R)).
  apply le_succ_l in R.
  apply lt_eq_cases in R.
  destruct R as [RL | RR].
  exists k, (S m0).
  firstorder.
  rewrite add_succ_r.
  rewrite<- L.
  reflexivity.

  exists (S k), 0.

  apply conj.
  apply (le_le_succ_r _ _ Hk).
  apply conj.
  rewrite L.
  rewrite<- add_succ_r.
  rewrite RR.
  rewrite add_0_r.
  apply sub_le_direct.
  apply (pow_nonneg _ _ n_ge0).
  apply lt_le_incl.
  apply (pow_succ_lt _ _ n_gt1 Hk).

  apply sub_lt_gt0.
  apply pow_nonneg.
  apply n_ge0.

  apply (pow_succ_lt _ _ n_gt1).
  apply (le_le_succ_r _ _ Hk).
Qed.

(** log n is exact on powers of n *)

Lemma log_pown : forall a, 0<=a -> log n (n^a) == a.
Proof.
  intros a Ha.
  
  apply log_unique.
  trivial.
  split.
  easy.
  apply (pow_succ_lt _ _ n_gt1 Ha).
Qed.

Lemma log_pred_pown : forall a, 0<a -> log n (P (n^a)) == P a.
Proof.
 intros a Ha.
 assert (Ha' : S (P a) == a) by (now rewrite lt_succ_pred with 0).
 apply log_unique.
 apply lt_succ_r; order.
 rewrite <-le_succ_l, <-lt_succ_r, Ha'.
 rewrite lt_succ_pred with 0.
 split; try easy. apply pow_lt_mono_r_iff; try order'.
 apply n_gt1.
 rewrite succ_lt_mono, Ha'. apply lt_succ_diag_r.
 apply pow_pos_nonneg.
 apply n_gt0.
 order'.
Qed.

Lemma log_1 : log n 1 == 0.
Proof.
 rewrite <- (pow_0_r n). now apply log_pown.
Qed.

Lemma log_n : log n n == 1.
Proof.
 rewrite<- (pow_1_r n) at 2.
 apply log_pown.
 rewrite one_succ.
 apply le_succ_diag_r.
Qed.

Lemma log_pos : forall a, n <= a -> 0 < log n a.
Proof.
  intros a Ha.
  assert (Ha' : 0 < a).
  apply (lt_le_trans _ n _). 
  apply n_gt0.
  exact Ha.
  assert (H := log_nonneg a).
  le_elim H.
  trivial.

  generalize (log_spec n a n_gt1 Ha'). 
  rewrite <- H in *. nzsimpl; try order.
  intros (H1,H2).
  
  apply nlt_ge in Ha.
  apply Ha in H2.
  contradiction.
Qed.

Lemma log_null : forall a, log n a == 0 <-> a < n.
Proof.
 intros a. split; intros H.

 destruct (lt_ge_cases a n) as [Ha|Ha]; trivial.
 generalize (log_pos a Ha); order.
 assert (H2 := le_gt_cases a 0).
 decompose [or] H2.
 apply (log_nonpos _ _ n_gt1 H0).

 apply log_unique.
 order'.
 rewrite pow_0_r.
 rewrite pow_succ_r.
 rewrite pow_0_r.
 rewrite mul_1_r.
 split.
 rewrite one_succ.
 apply le_succ_l.
 exact H0.
 exact H.
 easy.
Qed.

Lemma log_le_mono : forall a b, a<=b -> log n a <= log n b.
Proof.
 intros a b H.
 destruct (le_gt_cases a 0) as [Ha|Ha].
 rewrite (log_nonpos _ _ n_gt1); order_pos.
 assert (Hb : 0 < b) by order.
 destruct (log_spec _ a n_gt1 Ha) as (LEa,_).
 destruct (log_spec _ b n_gt1 Hb) as (_,LTb).
 apply lt_succ_r.
 apply (pow_lt_mono_r_iff n _ _ n_gt1).
 order_pos.
 order_pos.
Qed.


Lemma log_lt_cancel : forall a b, log n a < log n b -> a < b.
Proof.
 intros a b H.
 destruct (le_gt_cases b 0) as [Hb|Hb].
  rewrite (log_nonpos n b n_gt1) in H; trivial.
  generalize (log_nonneg a); order.
 destruct (le_gt_cases a 0) as [Ha|Ha]. order.
 destruct (log_spec n a n_gt1 Ha) as (_,LTa).
 destruct (log_spec n b n_gt1 Hb) as (LEb,_).
 apply le_succ_l in H.
 apply (pow_le_mono_r_iff n _ _ n_gt1) in H; order_pos.
Qed.


Lemma log_le_pown : forall a b, 0<a -> (n^b<=a <-> b <= log n a).
Proof.
 intros a b Ha.
 split; intros H.
 destruct (lt_ge_cases b 0) as [Hb|Hb].
 generalize (log_nonneg a); order.
 rewrite <- (log_pown b); trivial. now apply log_le_mono.
 transitivity (n^(log n a)).
 apply pow_le_mono_r.
 apply n_gt0.
 order'.
 now destruct (log_spec n a n_gt1 Ha).
Qed.

Lemma log_lt_pown : forall a b, 0<a -> (a<n^b <-> log n a < b).
Proof.
 intros a b Ha.
 split; intros H.
 destruct (lt_ge_cases b 0) as [Hb|Hb].
 rewrite pow_neg_r in H; order.
 apply (pow_lt_mono_r_iff n _ _ n_gt1); try order_pos.
 apply le_lt_trans with a; trivial.
 now destruct (log_spec n a n_gt1 Ha).
 destruct (lt_ge_cases b 0) as [Hb|Hb].
 generalize (log_nonneg a); order.
 apply log_lt_cancel; try order.
 rewrite log_pown.
 exact H.
 exact Hb.
Qed.

Lemma log_lt_lin : forall a, 0<a -> log n a < a.
Proof.
 intros a Ha.
 apply (pow_lt_mono_r_iff n _ _ n_gt1); try order_pos.
 apply le_lt_trans with a.
 now destruct (log_spec n a n_gt1 Ha).
 apply pow_gt_lin_r.
 apply n_gt1.
 order'.
Qed.

Lemma log_le_lin : forall a, 0<=a -> log n a <= a.
Proof.
 intros a Ha.
 le_elim Ha.
 now apply lt_le_incl, log_lt_lin.
 rewrite <- Ha, log_nonpos.
 easy.
 apply n_gt1.
 order.
Qed.

(** Log and multiplication. *)

(** Due to rounding error, we don't have the usual
    [log n (a*b) = log n a + log n b] but we may be off by 1 at most *)

Lemma log_mul_below : forall a b, 0<a -> 0<b ->
 log n a + log n b <= log n (a*b).
Proof.
 intros a b Ha Hb.
 apply log_le_pown; try order_pos.
 rewrite pow_add_r by order_pos.
 apply mul_le_mono_nonneg.
 apply pow_nonneg.
 apply n_ge0.
 
 apply (log_spec n a n_gt1).
 exact Ha.

 apply pow_nonneg.
 apply n_ge0.
 apply (log_spec n b n_gt1).
 exact Hb.
Qed.

Lemma log_mul_above : forall a b, 0<=a -> 0<=b ->
 log n (a*b) <= log n a + log n b + 1.
Proof.
 intros a b Ha Hb.
 le_elim Ha.
 le_elim Hb.
 apply lt_succ_r.
 rewrite add_1_r, <- add_succ_r, <- add_succ_l.
 apply log_lt_pown; try order_pos.
 rewrite pow_add_r by order_pos.
 apply mul_lt_mono_nonneg; try order; now apply (log_spec n _ n_gt1).
 rewrite <- Hb. nzsimpl. rewrite log_nonpos.
 apply le_le_succ_r.
 rewrite add_0_r.
 apply log_nonneg.
 apply n_gt1.
 easy.
 rewrite <- Ha.
 nzsimpl. 
rewrite (log_nonpos n 0 n_gt1); order_pos.
Qed.

Lemma log_mul_pown : forall a b, 0<a -> 0<=b -> log n (a*n^b) == b + log n a.
Proof.
  intros a b Ha Hb.
  apply log_unique; try order_pos. 
  split.
  rewrite pow_add_r, mul_comm; try order_pos.
  apply mul_le_mono_nonneg_r. 
  apply (pow_nonneg _ _ n_ge0). 
  now apply (log_spec n _ n_gt1).
  rewrite <-add_succ_r, pow_add_r, mul_comm; try order_pos.
  apply mul_lt_mono_pos_l. 
  apply (pow_pos_nonneg _ _ n_gt0 Hb).
  now apply (log_spec n _ n_gt1).
Qed.

Lemma log_muln : forall a, 0<a -> log n (n*a) == S (log n a).
Proof.
 intros a Ha. 
 generalize (log_mul_pown a 1 Ha le_0_1). 
 rewrite pow_1_r.
 rewrite add_1_l.
 rewrite mul_comm.
 firstorder.
Qed.

(** Two numbers with same log n cannot be far away. *)

Lemma log_same : forall a b, 0<a -> 0<b -> log n a == log n b -> a < n*b.
Proof.
 intros a b Ha Hb H.
 apply log_lt_cancel. rewrite log_muln, H by trivial.
 apply lt_succ_diag_r.
Qed.

Lemma log_succ_le : forall a, log n (S a) <= S (log n a).
Proof.
 intros a.
 destruct (lt_trichotomy 0 a) as [LT|[EQ|LT]].
 apply (pow_le_mono_r_iff n _ _ n_gt1); try order_pos.
 transitivity (S a).
 apply (log_spec n _ n_gt1).
 apply lt_succ_r; order.
 now apply le_succ_l, (log_spec n _ n_gt1).
 rewrite <- EQ, <- one_succ, log_1; order_pos.
 rewrite (log_nonpos n a n_gt1). 
 rewrite (log_nonpos n (S a) n_gt1).
 order_pos.
 now rewrite le_succ_l.
 order_pos.
Qed.

Lemma log_succ_or : forall a,
 log n (S a) == S (log n a) \/ log n (S a) == log n a.
Proof.
 intros.
 destruct (le_gt_cases (log n (S a)) (log n a)) as [H|H].
 right. generalize (log_le_mono _ _ (le_succ_diag_r a)); order.
 left. apply le_succ_l in H. generalize (log_succ_le a); order.
Qed.

Lemma log_eq_succ_is_pown : forall a,
 log n (S a) == S (log n a) -> exists b, S a == n^b.
Proof.
 intros a H.
 destruct (le_gt_cases a 0) as [Ha|Ha].
 
 assert (Hn := n_gt1).
 rewrite 2 (proj2 (log_null _)) in H. 
 generalize (lt_succ_diag_r 0); order.
 order'. 
 assert (Ha2 : S a <= 1).
 rewrite one_succ.
 apply ((proj1 (succ_le_mono _ _)) Ha).
 order.

 assert (Ha' : 0 < S a) by (apply lt_succ_r; order).
 exists (log n (S a)).
 generalize (proj1 (log_spec n (S a) n_gt1 Ha')) (proj2 (log_spec n a n_gt1 Ha)).
 rewrite <- le_succ_l, <- H. order.
Qed.

Lemma log_eq_succ_iff_powb : forall a, 0<a ->
 (log n (S a) == S (log n a) <-> exists b, S a == n^b).
Proof.
 intros a Ha.
 split. apply log_eq_succ_is_pown.
 intros (b,Hb).
 assert (Hb' : 0 < b).
  apply (pow_gt_1 n _ n_gt1); try order'; now rewrite <- Hb, one_succ, <- succ_lt_mono.
 rewrite Hb, log_pown; try order'.
 setoid_replace a with (P (n^b)). rewrite log_pred_pown; trivial.
 symmetry; now apply lt_succ_pred with 0.
 apply succ_inj. rewrite Hb. symmetry. apply lt_succ_pred with 0.
  rewrite <- Hb, lt_succ_r; order.
Qed.

Lemma mul_n_mono_l:
  forall a b : t, a < b -> 1 + n * a < n * b.
Proof.
  intros a b Hab.
  apply le_succ_l in Hab.
  apply (lt_le_trans _ (n * S a) _).
  rewrite mul_succ_r; rewrite add_comm; apply add_lt_mono_l.
  apply n_gt1.
  apply (mul_le_mono_nonneg_l _ _ _ n_ge0).
  exact Hab.
Qed.

Lemma log_succ_muln : forall a, 0<a -> log n (n*a+1) == S (log n a).
Proof.
  intros a Ha.
  rewrite add_1_r.
  destruct (log_succ_or (n*a)) as [H|H]; [exfalso|now rewrite H, log_muln].
  apply log_eq_succ_is_pown in H. destruct H as (b,H).
  destruct (lt_trichotomy b 0) as [LT|[EQ|LT]].
  rewrite pow_neg_r in H; trivial.
  apply (mul_pos_pos n), succ_lt_mono in Ha; try order'.
  rewrite <- one_succ in Ha. order'.
  apply n_gt0.
  rewrite EQ, pow_0_r in H.
  apply (mul_pos_pos n _ n_gt0), succ_lt_mono in Ha; try order'.
  rewrite <- one_succ in Ha. order'.
  assert (EQ:=lt_succ_pred 0 b LT).
  rewrite <- EQ, pow_succ_r in H; [|now rewrite <- lt_succ_r, EQ].
  destruct (lt_ge_cases a (n^(P b))) as [LT'|LE'].
  generalize (mul_n_mono_l _ _ LT'). rewrite add_1_l. order.
  rewrite (mul_le_mono_pos_l _ _ n) in LE'; try order'.
  rewrite <- H in LE'. apply le_succ_l in LE'. order.
  apply n_gt0.
Qed.

(** Log and addition *)

(* The proof for log_add_le needs to be rethought.  The reliance on
the value two is too strong. *)

Lemma log_add_le : forall a b, a~=1 -> b~=1 -> log n (a+b) <= log n a + log n b.
Proof.
 intros a b Ha Hb.
 destruct (lt_trichotomy a 1) as [Ha'|[Ha'|Ha']]; [|order|].
 rewrite one_succ, lt_succ_r in Ha'.
 rewrite (log_nonpos _ a n_gt1); trivial. nzsimpl. apply log_le_mono.
 rewrite <- (add_0_l b) at 2. now apply add_le_mono.
 destruct (lt_trichotomy b 1) as [Hb'|[Hb'|Hb']]; [|order|].
 rewrite one_succ, lt_succ_r in Hb'.
 rewrite (log_nonpos n b n_gt1); trivial. nzsimpl. apply log_le_mono.
 rewrite <- (add_0_r a) at 2. now apply add_le_mono.
 clear Ha Hb.
 apply lt_succ_r.
 apply log_lt_pown; try order_pos.
 rewrite pow_succ_r by order_pos.
 apply (lt_le_trans _ (2 * n ^ (log n a + log n b)) _).
 rewrite two_succ, one_succ at 1. nzsimpl.
 apply add_lt_mono.

 apply lt_le_trans with (n^(S (log n a))). apply (log_spec _ _ n_gt1); order'.
 apply pow_le_mono_r. apply n_gt0. rewrite <- add_1_r. apply add_le_mono_l.
 rewrite one_succ.
 now apply le_succ_l, log_pos.
 apply lt_le_trans with (n^(S (log n b))). apply log_spec; order'.
 apply pow_le_mono_r. order'. rewrite <- add_1_l. apply add_le_mono_r.
  rewrite one_succ; now apply le_succ_l, log_pos.
Qed.



End N.


End NLogProp.

(* Local Variables: *)
(* coq-prog-name: "/usr/local/bin/coqtop" *)
(* coq-load-path: nil *)
(* End: *)
