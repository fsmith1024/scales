
(** * Cardinality 

  A simple definition of cardinality of a proposition.

 *)

Require Import Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import List.
Require Import ListSet.

Require Import Elementary.

Import ListNotations.

Lemma list_cardinality:
  forall A:Type, forall L1 L2 : list A,
    ((forall a:A, In a L1 <-> In a L2) /\ NoDup L1 /\ NoDup L2) 
    -> (length L1 = length L2).
Proof.
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
Proof.
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
Proof.
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
