Require Import NZAxioms NZMulOrder NZDomain.
Require Import Psatz.

Module Type NZSubProp 
       (Import A : NZOrdAxiomsSig')
       (Import B : NZMulOrderProp A).

Module T := NZDomainProp A.

Lemma iter_assoc:
  forall m:nat, forall A : Type, forall f: A -> A, forall a:A,
    f ((nat_iter m f) a) = (nat_iter m f) (f a).
Proof.
  intro m.
  induction m.
  simpl.
  easy.

  intros A f a.
  simpl.
  rewrite IHm.
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
Lemma pred_lt: forall z m : t, z < m -> P m < m.
Proof.
  intros z m Hmz.
  apply succ_lt_mono.
  rewrite (lt_succ_pred _ _ Hmz).
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
  clear H0 H2 H5 H7 n a1 n0 a0 H1 H6.

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
  forall m : nat, forall a:t, (nat_iter m P) ((nat_iter m S) a) == a.
Proof.
  intro m.
  induction m.
  simpl.
  easy.

  intro a.
  simpl.
  rewrite (iter_assoc _ _ P).
  rewrite pred_succ.

  apply IHm.
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


End NZSubProp.

