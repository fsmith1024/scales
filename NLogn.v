
Require Import NZAxioms NZMulOrder NZPow.
Require Import Psatz.

Module Type Log (Import A: Typ).
  Parameter Inline log : t -> t -> t.
End Log.

Module Type NLogSpec (A: NZOrdAxiomsSig') (B: Pow' A) (C: Log A).
  Import A B C.

  Axiom log_spec: forall n a, n > 1 -> 0 < a -> n^(log n a) <= a < n^(S (log n a)).
  Axiom log_nonpos: forall n a, n>1 -> a<=0 -> log n a = 0.

End NLogSpec.

Module Type NLog (A : NZOrdAxiomsSig) (B : Pow A) := Log A <+ NLogSpec A B.

Module Type NLogProp 
       (Import A : NZOrdAxiomsSig')
       (Import B : NZPow' A)
       (Import C : NLog A B)
       (Import D : NZMulOrderProp A)
       (Import E : NZPowProp A B D).

Section N.

Parameter n : t.

Axiom n_gt1 : n > 1.

Lemma n_gt0 : n > 0.
Proof.
  assert (H:= n_gt1).
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

(* Stopped here: We are simply replicated Coqs code for NZLog because
that code only handles powers of 2.  So far th translation has been
mechanical. log_exists below is my own proof, but induction doesn't work since Z doesn't terminate. *)

(* 
Lemma log_unique' : forall a b c, 0<=b -> 0<=c<2^b ->
 a == 2^b + c -> (log n) a == b.
Proof.
 intros a b c Hb (Hc,H) EQ.
 apply log_unique. trivial.

 split.
 rewrite <- add_0_r at 1. now apply add_le_mono_l.
 rewrite pow_succ_r by order.
 rewrite two_succ at 2. nzsimpl. now apply add_lt_mono_l.
Qed.
*)

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

(* This is a very stupid result basically equivalent to lt_succ_pred. *)
Lemma pred_lt: forall z n : t, z < n -> P n < n.
Proof.
  intros z n Hnz.
  apply succ_lt_mono.
  rewrite (lt_succ_pred _ _ Hnz).
  apply lt_succ_diag_r.
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

Lemma ored_inj: forall za zb a b :t, za < a -> zb < b -> P a == P b -> a == b.
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

Lemma pred_succ_le: forall a b z: t, z < (b - a) -> (b - a) <= (S b - a).
Proof.

Qed.


Lemma xxx: forall a b : t, (S b - S a) ==  (b - a).
Proof.
  apply (bi_induction (fun a => forall b: t, (S b - S a) == (b -a))).
  solve_proper.

  intros b.

  rewrite sub_0_r.
  rewrite sub_succ_r.
  rewrite sub_0_r.
  rewrite pred_succ.
  reflexivity.

  intro a.
  apply conj.

  intros IH b.
  
  rewrite sub_succ_r.
  rewrite (sub_succ_r b a).
  apply pred_wd.
  apply IH.

  intros IH b.
  assert (IHs := IH b).
  rewrite sub_succ_r in IHs.
  rewrite (sub_succ_r b a) in IHs.
  

  assert (IHs := IH (S b) z).


  rewrite sub_succ_r.

  rewrite sub_succ_r.

  
  rewrite sub_succ_r in Hzb.

  apply (lt_trans _ (pred_lt z (b - a) Hzb)
Qed.
 
Lemma aaa: forall a b z k : t, z < k -> a + k == b -> k == (b - a).
Proof.
apply (bi_induction (fun a => forall b z k : t, z < k -> a + k == b -> k == (b - a))).

solve_proper.

intros b z k Hzk Hkb.
rewrite add_0_l in Hkb.
rewrite sub_0_r.
exact Hkb.

intro a.
apply conj.

intros IH b z k Hzk Hak.

rewrite add_succ_comm in Hak.
assert (Hzk' := (lt_trans _ _ _ Hzk (lt_succ_diag_r _))).
assert (IHs := IH b z (S k) Hzk' Hak).
apply pred_wd in IHs.
rewrite pred_succ in IHs.
rewrite IHs.
rewrite sub_succ_r.
easy.

intros IH b z k Hzk Hbk.


intros IH.

apply (bi_induction (fun b:t =>forall z k : t, z < k -> a + k == b -> k == b - a)).
solve_proper.

intros z k Hzk Hak.







Qed.

Lemma aaa: forall a:t, forall z k : t, z < k -> forall b : t, a + k == b -> k == (b - a).
Proof.

apply (bi_induction (fun a => forall z k : t, z < k -> forall b : t, a + k == b -> k == (b - a))).

solve_proper.

intros z k Hzk b Hkb.
rewrite<- Hkb.
rewrite add_0_l; rewrite sub_0_r.
easy.

intros a.
apply conj.

intros IH z k Hzk b Hkb.
rewrite sub_succ_r.
rewrite <- (IH z (S k)).
rewrite pred_succ.
easy.

apply (lt_trans _ _ _ Hzk (lt_succ_diag_r _)).

rewrite<- add_succ_comm.
exact Hkb.

intros IH z k Hzk b Hkb.

assert (IHs := IH z (P k) _ b).






Qed.

 
Lemma yyy: forall a b : t, a <= b -> a + (b - a) == b.
Proof.
  apply (bi_induction (fun a:t => forall b : t, a <= b -> a + (b - a) == b)).

  solve_proper.

  intros b Hb.
  rewrite add_0_l.
  rewrite sub_0_r.
  reflexivity.

  intro a.
  apply conj.

  intros IH b HSba.
  rewrite sub_succ_r.
  apply le_succ_l in HSba.
  assert (Hba :=  (lt_le_incl  _ _ HSba)).
  assert (IHs := IH b Hba).
  assert (H:= lt_plus_0 a b (b - a) HSba IHs).
  rewrite add_succ_comm.
  rewrite (lt_succ_pred _ _ H).
  exact IHs.

  intros IH b Hba.
  
  


Qed.

Lemma xxx: forall n:t, 0 < n -> forall m : t, m >= n -> S m - n == S (m - n).
Proof.
  apply (order_induction_0 (fun n => 0 < n -> forall m : t, m >= n -> S m - n == S (m - n))).
  solve_proper.

  intro H.
  apply lt_irrefl in H.
  contradiction.

  intros n Hn IH Hn2 m Hnm.
  
  assert (Hcases:= lt_total n 0).
  destruct Hcases.
  apply le_ngt in Hn.
  exfalso.
  apply Hn.
  exact H.

  decompose [or] H.
  rewrite H0 in *.
  rewrite sub_succ_r.
  rewrite sub_0_r.
  rewrite pred_succ.
  rewrite sub_succ_r.
  rewrite sub_0_r.
  rewrite (lt_succ_pred 0).
  reflexivity.
  order.

  rewrite sub_succ_r.
  rewrite sub_succ_r.
  
  apply le_succ_l in Hnm.
  apply lt_le_incl in Hnm.
  assert (H2:= IH H0 m Hnm).
  rewrite H2.
  
  assert (Hcases := lt_total (S n) m).
  decompose [or] Hcases.

  

  




Qed.

Lemma plus_sub_eq:
  forall a b c:t, a + b == c -> b == (c -a).
Proof.
  apply (order_induction_0 (fun x:t => (forall b c:t, (x + b == c) -> b == (c - x)))).
  intros x y Hxy.
  apply conj.
  intros H b c.
  rewrite<- Hxy.
  firstorder.

  intros H b c.
  rewrite Hxy.
  firstorder.

  intros b c.
  rewrite sub_0_r.
  rewrite add_0_l.
  firstorder.
  
  intros n Hn IH b c H.
  rewrite sub_succ_r.
  rewrite add_succ_comm in H.
  assert (IHs := (IH (S b) c H)).
  rewrite<- IHs.
  rewrite pred_succ.
  easy.

  intros n Hn IH b c H.
  apply succ_inj_wd in H.
  rewrite<- add_succ_l in H.
  assert (IHs := IH b (S c) H).
  rewrite sub_succ_r in IHs.
  

  


  






Qed.

Lemma plus_sub:
  forall a b:t, b > a -> a + (b - a) == b.
Proof.
  intros a b.
  apply (lt_ind (fun x => a + (x - a) == x)).
  intros x y Hxy.
  rewrite Hxy.
  firstorder.
  

  







Qed.

Lemma log_exists:
    forall a:t,
      a>0 -> exists k m:t, (a == n^k + m) /\ m < (n^(S k) - n^k).
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
  destruct H as (L,R).
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
  rewrite L.
  rewrite<- add_succ_r.
  rewrite RR.





  
  assert (H: (S m0) <= (n ^ (S k) - n ^ k)).
  

  

Qed.

(** log n is exact on powers of n *)

Lemma log_pown : forall a, 0<=a -> log n (n^a) == a.
Proof.
 intros a Ha.
 apply log_unique n with 0; trivial.
 split; order_pos. now nzsimpl.
Qed.



(* Stopped here *)













induction a.
lia.
intro H0.
assert (Hcases: a = 0 \/ a > 0).
lia.
decompose [or] Hcases.
rewrite H in *.
exists 0.
exists 0.
simpl.
apply conj.
auto.
lia.

(* Interesting case *)
assert (IHa' := IHa H).
destruct IHa' as [k'].
destruct H1 as [m'].
decompose [and] H1.
clear H1.
clear Hcases.
assert (Hcases: ((S m') = b ^ (S k') - b ^ k') \/ (S m') < b ^ (S k') - b ^ k').
lia.
decompose [or] Hcases.
exists (S k').
exists 0.
rewrite H2.
apply conj.
rewrite plus_n_Sm.
rewrite H1.
lia.
simpl.
assert (Hbase := base_gt1).
rewrite mult_assoc.
rewrite<- mult_minus_distr_r.
apply Nat.mul_pos_pos.
rewrite<- (mult_1_r b) at 3.
rewrite<- mult_minus_distr_l.
apply Nat.mul_pos_pos.
lia.
lia.
apply (lt_le_trans _ 1 _).
lia.
rewrite<- (pow_0_r b).
apply Nat.pow_le_mono_r_iff.
exact Hb1.
lia.

exists (k'); exists (S m').
apply conj.
rewrite H2.
lia.
exact H1.
Qed.


End N.


End NLogProp.

Module Type N.
  Parameter n:nat. 
  Axiom base_gt1: n>1.
End N.

Module Type NLognSpec(Import A : N). 

  Parameter logn : nat -> nat.

  Axiom logn_spec: forall a, 0<a -> n^(logn a) <= a < n^(S (logn a)).
  Axiom logn_0: logn 0 = 0.

End NLognSpec.

(* We need log3 not log2, so we just copy the standard library
definition but generalize from 2 to n.  This code special-cases Nat
but presumably would not be hard to generlize to Z as well. *) 

Module NLogn(Import A : N).

Lemma base_gt0: 0 < n.
Proof.
assert (H := base_gt1).
lia.
Qed.

Lemma base_nonzero: n <> 0.
Proof.
  assert(H := base_gt1).
  lia.
Qed.

Lemma mul_lt_r: 
  forall a b :nat ,
    a>0 -> b>1 -> a < b * a.
Proof.
  intros a b Ha Hb.
  rewrite<- (mult_1_r a) at 1.
  rewrite mult_comm at 1.
  apply mult_lt_compat_r.
  exact Hb.
  exact Ha.
Qed.

Fixpoint logn_iter (k:nat) (a:nat) :=
  match k with
    | 0 => 0
    | (S k') => 
      match nat_compare (n^k') a with
        | Eq => k'
        | Lt => k'
        | Gt => logn_iter k' a
      end
  end.

Lemma logn_iter_basic: forall b k:nat, k > 0 -> b > k -> (logn_iter b (n^k)) = k.
Proof.
  intro b.
  induction b.
  simpl.
  intro k.
  lia.

  intro k.
  intros Hk Hb.
  unfold logn_iter.
  fold logn_iter.
  remember (nat_compare (n ^ b) (n ^ k)) as w.
  symmetry in Heqw.
  
  case w in *.
  
  (* = *)
  apply nat_compare_eq_iff in Heqw.
  apply (Nat.pow_inj_r n _ _ base_gt1 Heqw).

  (* < *)
  apply nat_compare_lt in Heqw.
  apply Nat.pow_lt_mono_r_iff in Heqw.
  lia.
  apply base_gt1.
  
  (* > *)
  apply nat_compare_gt in Heqw.
  apply Nat.pow_lt_mono_r_iff in Heqw.
  apply IHb.
  exact Hk.
  exact Heqw.
  exact base_gt1.
Qed.

Lemma logn_iter_basic2: 
  forall b k m:nat,
    b > k -> m < (n ^ (S k) - n ^ k) -> (logn_iter b (n^k + m)) = k.
Proof.
  intro b.
  induction b.
  
  simpl.
  intros k m.
  lia.
  
  intros k m Hb Hm.
  unfold logn_iter; fold logn_iter.
  remember (nat_compare _ _) as w.
  symmetry in Heqw.

  case w in *.

  (* = *)
  apply nat_compare_eq in Heqw.
  assert (H: n^b < n^ (S k)).
  lia.
  apply Nat.pow_lt_mono_r_iff in H.
  lia.
  exact base_gt1.
  
  (* < *)
  apply nat_compare_lt in Heqw.
  assert (H: n^b < n ^ (S k)).
  lia.
  apply Nat.pow_lt_mono_r_iff in H.
  lia.
  exact base_gt1.

  (* >= *)
  apply nat_compare_gt in Heqw.
  apply IHb.
  assert (H : k = b \/ k < b).
  lia.
  decompose [or] H.
  rewrite H0 in Heqw.
  lia.
  exact H0.
  exact Hm.
Qed.

Lemma logn_exists:
  forall b : nat, 
    b>1 ->
    forall a:nat,
      a>0 -> exists k m:nat, (a = b^k + m) /\ m < (b^(S k) - b^k).
Proof.
intros b Hb1 a.
induction a.
lia.
intro H0.
assert (Hcases: a = 0 \/ a > 0).
lia.
decompose [or] Hcases.
rewrite H in *.
exists 0.
exists 0.
simpl.
apply conj.
auto.
lia.

(* Interesting case *)
assert (IHa' := IHa H).
destruct IHa' as [k'].
destruct H1 as [m'].
decompose [and] H1.
clear H1.
clear Hcases.
assert (Hcases: ((S m') = b ^ (S k') - b ^ k') \/ (S m') < b ^ (S k') - b ^ k').
lia.
decompose [or] Hcases.
exists (S k').
exists 0.
rewrite H2.
apply conj.
rewrite plus_n_Sm.
rewrite H1.
lia.
simpl.
assert (Hbase := base_gt1).
rewrite mult_assoc.
rewrite<- mult_minus_distr_r.
apply Nat.mul_pos_pos.
rewrite<- (mult_1_r b) at 3.
rewrite<- mult_minus_distr_l.
apply Nat.mul_pos_pos.
lia.
lia.
apply (lt_le_trans _ 1 _).
lia.
rewrite<- (pow_0_r b).
apply Nat.pow_le_mono_r_iff.
exact Hb1.
lia.

exists (k'); exists (S m').
apply conj.
rewrite H2.
lia.
exact H1.
Qed.

Lemma mul_super_linear:
  forall a b c : nat, a > 1 -> a * b < c -> b < c.
Proof.
  intros a b c Ha.
  induction b.
  lia.
  intro H.
  rewrite mult_succ_r in H.
  assert (H2 : a * b < c).
  lia.
  assert (H3 := IHb H2).
  assert (Hcases: (S b) = c \/ (S b) < c).
  lia.
  decompose [or] Hcases.
  clear Hcases.
  rewrite<- H0 in H.
  replace (S b) with (b + 1) in H.
  apply Nat.add_lt_cases in H.
  decompose [or] H.
  clear H.
  case b in *.
  lia.
  rewrite<- H0 in H2.
  replace (a * S b) with ((S b) + (pred a) * (S b)) in H2.
  replace (S (S b)) with ((S b) + 1) in H2.
  apply Nat.add_lt_mono_l in H2.
  assert (Hpred: pred a > 0).
  lia.
  assert (Hblah: pred a * S b = 0).
  lia.
  apply mult_is_O in Hblah.
  decompose [or] Hblah.
  lia.
  lia.
  lia.
  rewrite<- (mult_1_r (S b)) at 1.
  rewrite mult_comm at 1.
  rewrite<- mult_plus_distr_r.
  replace (1 + pred a) with a.
  reflexivity.
  lia.
  lia.
  lia.
  lia.
Qed.

Lemma pow_super_linear:
  forall a b c : nat, a>1 -> a^b < c -> b < c.
Proof.
intros a b c Ha.
induction b.
lia.
simpl.
intro Hab.

assert (H := mul_super_linear _ _ _ Ha Hab).
assert (H2 := IHb H).

case c in *.
lia.
apply lt_n_S.

assert (Hcases: b < c \/ b = c).
lia.
decompose [or] Hcases.
exact H0.

rewrite<- H0 in Hab.
assert (Hx:= Nat.pow_gt_lin_r a (S b) Ha).
simpl in Hx.
lia.
Qed.

Lemma logn_iter_spec: 
  forall k a:nat, 
    a > 0 -> k > a -> 
    n^(logn_iter k a) <= a < n^(S (logn_iter k a)).
Proof.
  intros k a Ha Hk.
  assert (H := logn_exists n base_gt1 a Ha).
  destruct H as [k'].
  destruct H as [m'].
  decompose [and] H.
  
  remember (logn_iter k a) as logn_a.
  rewrite H0 in Heqlogn_a.
  rewrite logn_iter_basic2 in Heqlogn_a.
  rewrite Heqlogn_a.
  lia.
  rewrite H0 in Hk.
  
  replace k with (k + 0) in Hk.
  apply Nat.add_lt_cases in Hk.
  decompose [or] Hk.
  apply pow_super_linear in H2.
  exact H2.
  exact base_gt1.
  lia.
  lia.
  exact H1.
Qed.

Definition logn a:nat := logn_iter (S a) a.

Lemma logn_spec: 
  forall a:nat, a > 0 -> n^(logn a) <= a < n^(S (logn a)).
Proof.
  intros a Ha.
  unfold logn.
  assert (H: S a > a).
  lia.
  apply (logn_iter_spec (S a) a Ha H).
Qed.

Lemma le_div_mul :
  forall s p q :nat, s>0 -> p <= q/s -> s*p <= q.
Proof.
intros s p q H0 H.
apply (le_trans _ (s * (q/s)) _).
apply mult_le_compat_l.
exact H.
apply Nat.mul_div_le.
lia.
Qed.

(* 
   
*)
Lemma lt_div_mul : 
  forall s p q :nat, s>0 -> p/s < q -> p < s*(S q).
Proof.
intros s p q H0 H.
rewrite mult_succ_r.
rewrite (div_mod p s).
apply plus_lt_compat.
apply mult_lt_compat_l.
exact H.
exact H0.
apply Nat.mod_upper_bound.
lia.
lia.
Qed.

Lemma lt_div_mul_r :
  forall s p q r : nat,
    s>0 -> r > q -> p/s < q -> p < s * r.
Proof.
  intros s p q r Hs Hr Hp.
  apply (lt_le_trans _ (s * (S q)) _).
  apply lt_div_mul.
  exact Hs.
  exact Hp.
  apply mult_le_compat_l.
  lia.
Qed.

Lemma le_lt_div_mul : 
  forall s p q t r: nat,
    s>0 ->
    r > t ->
    p <= q/s < t ->
    s*p <= q < s*r.
Proof.
intros s p q t r H0 Hr H.
decompose [and] H.
clear H.
apply conj.
apply le_div_mul.
exact H0.
exact H1.
apply (lt_div_mul_r s q t r).
exact H0.

lia.
exact H2.
Qed.

End NLogn.


(* Local Variables: *)
(* coq-prog-name: "/usr/local/bin/coqtop" *)
(* coq-load-path: nil *)
(* End: *)
