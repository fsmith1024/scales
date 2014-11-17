Require Import NZAxioms NZMulOrder NZPow NZDomain.
Require Import Psatz.
Require Import NZSub.

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
       (Import E : NZPowProp A B D)
       (Import F : NZSubProp A D).

(** A tactic for proving positivity and non-negativity *)

Ltac order_base :=
  (apply add_pos_pos
         || apply add_nonneg_nonneg 
         || apply mul_pos_pos 
         || apply mul_nonneg_nonneg 
         || apply pow_nonneg 
         || apply pow_pos_nonneg 
         || apply (le_le_succ_r 0)).

(* in case of success of an apply, we recurse *)
Ltac order_pos := (order_base; order_pos)  || order'.

Section N.

Variable n : t.

Hypothesis n_gt1 : n > 1.

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


(** order_pos *)

Ltac order_pos_log := 
  ((order_base || (apply log_nonneg)); order_pos_log) || order'.


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
  now apply le_le_succ_r.
  assert (b <= log n a).
  apply lt_succ_r, (pow_lt_mono_r_iff n); try order'.
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
(* Detour: Subtraction is very underspecified.  Not sure why but it is
a major road block. *)

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
 rewrite (log_nonpos _ _ n_gt1); order_pos_log.
 assert (Hb : 0 < b) by order.
 destruct (log_spec _ a n_gt1 Ha) as (LEa,_).
 destruct (log_spec _ b n_gt1 Hb) as (_,LTb).
 apply lt_succ_r.
 apply (pow_lt_mono_r_iff n _ _ n_gt1).
 order_pos_log.
 order_pos_log.
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
 apply (pow_le_mono_r_iff n _ _ n_gt1) in H; order_pos_log.
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
 rewrite pow_add_r by order_pos_log.
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
 rewrite pow_add_r by order_pos_log.
 apply mul_lt_mono_nonneg; try order; now apply (log_spec n _ n_gt1).
 rewrite <- Hb. nzsimpl. rewrite log_nonpos.
 apply le_le_succ_r.
 rewrite add_0_r.
 apply log_nonneg.
 apply n_gt1.
 easy.
 rewrite <- Ha.
 nzsimpl. 
 rewrite (log_nonpos n 0 n_gt1); order_pos_log.
Qed.

Lemma log_mul_pown : forall a b, 0<a -> 0<=b -> log n (a*n^b) == b + log n a.
Proof.
  intros a b Ha Hb.
  apply log_unique; try order_pos_log. 
  split.
  rewrite pow_add_r, mul_comm; try order_pos_log.
  apply mul_le_mono_nonneg_r. 
  apply (pow_nonneg _ _ n_ge0). 
  now apply (log_spec n _ n_gt1).
  rewrite <-add_succ_r, pow_add_r, mul_comm; try order_pos_log.
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
 apply (pow_le_mono_r_iff n _ _ n_gt1); try order_pos_log.
 transitivity (S a).
 apply (log_spec n _ n_gt1).
 apply lt_succ_r; order.
 now apply le_succ_l, (log_spec n _ n_gt1).
 rewrite <- EQ, <- one_succ, log_1; order_pos_log.
 rewrite (log_nonpos n a n_gt1). 
 rewrite (log_nonpos n (S a) n_gt1).
 order_pos_log.
 now rewrite le_succ_l.
 order_pos_log.
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
  rewrite EQ, pow_0_r in H.
  apply (mul_pos_pos n _ n_gt0), succ_lt_mono in Ha; try order'.
  rewrite <- one_succ in Ha. order'.
  assert (EQ:=lt_succ_pred 0 b LT).
  rewrite <- EQ, pow_succ_r in H; [|now rewrite <- lt_succ_r, EQ].
  destruct (lt_ge_cases a (n^(P b))) as [LT'|LE'].
  generalize (mul_n_mono_l _ _ LT'). rewrite add_1_l. order.
  rewrite (mul_le_mono_pos_l _ _ n) in LE'; try order'.
  rewrite <- H in LE'. apply le_succ_l in LE'. order.
Qed.

(** Log and addition *)

Lemma mul_le_mono_pos_l:
  forall a b c d : t, 0 < a -> a < b -> 0 < c -> c <= d -> a * c < b * d.
Proof.
  intros a b c d Ha Hb Hc Hd.
  apply lt_eq_cases in Hd.
  destruct Hd as [Hlt | Heq ].
  apply mul_lt_mono_nonneg.
  try order_pos_log.
  exact Hb.
  order_pos_log.
  exact Hlt.
  rewrite Heq.
  apply mul_lt_mono_pos_r.
  order_pos_log.
  exact Hb.
Qed.

Lemma log_add_le : forall a b, a>=n -> b>=n -> log n (a+b) <= log n a + log n b.
Proof.
  intros a b Ha Hb.
  assert (Hn := n_gt1).
  destruct (lt_trichotomy a 1) as [Ha'|[Ha'|Ha']]; [|order|].
  rewrite one_succ, lt_succ_r in Ha'.
  rewrite (log_nonpos _ a n_gt1); trivial. nzsimpl. apply log_le_mono.
  rewrite <- (add_0_l b) at 2. now apply add_le_mono.
  destruct (lt_trichotomy b 1) as [Hb'|[Hb'|Hb']]; [|order|].
  rewrite one_succ, lt_succ_r in Hb'.
  rewrite (log_nonpos n b n_gt1); trivial. nzsimpl. apply log_le_mono.
  rewrite <- (add_0_r a) at 2. now apply add_le_mono.
  
  assert (Ha0 : a > 0).
  order_pos_log.
  assert (Has := log_spec n a n_gt1 Ha0).
  assert (Hb0 : b > 0).
  order_pos_log.
  assert (Hbs := log_spec n b n_gt1 Hb0).
  clear Ha0 Hb0.
  
  apply lt_succ_r.
  apply log_lt_pown; try order_pos_log.
  
  apply (lt_le_trans _ (n ^ S (log n a) + n ^ S (log n b)) _).
  apply add_lt_mono.
  apply (proj2 Has).
  apply (proj2 Hbs).
  
  rewrite pow_succ_r by order_pos_log.
  rewrite pow_succ_r by order_pos_log.
  rewrite pow_succ_r by order_pos_log.
  rewrite<- mul_add_distr_l.
  
  assert (Hloga := log_nonneg a).
  assert (Hlogb := log_nonneg b).
  
  apply (mul_le_mono_nonneg_l _ _ _ n_ge0).
  rewrite pow_add_r by order_pos_log.
  
  apply add_le_mul.
  apply pow_gt_1; try order_pos_log.
  apply log_pos; try order_pos_log.
  apply pow_gt_1; try order_pos_log.
  apply log_pos; try order_pos_log.
Qed.

(* The proof for add_log_lt needs to be rethought.  The reliance on
the value two is too strong. *)

(* 

Without loss of generality assume a >= b,
  log n a + log n b <= 2 * log n a <= 2 * log n (a + b)
  

*)
Lemma add_log_lt : 
  forall a b, 
    0 < a -> 0 < b -> log n a + log n b <= 2*log n (a+b).
Proof.
  intros a b Ha Hb.
  destruct (le_gt_cases a b) as [H | H ].
  apply log_le_mono in H.
  apply (le_trans _ (log n b + log n b) _).
  apply add_le_mono_r; exact H.
 
  rewrite two_succ.
  rewrite mul_succ_l.
  rewrite mul_1_l.
  apply add_le_mono.
  apply log_le_mono. 
  rewrite<- add_0_l at 1.
  apply (add_le_mono_r 0 a b).
  order_pos_log.

  apply log_le_mono.
  rewrite<- add_0_l at 1.
  apply (add_le_mono_r 0 a b).
  order_pos_log.

  assert (H' : b <= a) by order_pos_log.
  apply (le_trans _ (log n a + log n a) _).
  apply log_le_mono in H'.
  apply add_le_mono_l; exact H'.
  
  rewrite two_succ; rewrite mul_succ_l.
  rewrite mul_1_l.
  apply add_le_mono.
  apply log_le_mono.
  rewrite<- add_0_l at 1.
  rewrite add_comm.
  apply add_le_mono_l.
  order_pos_log.

  apply log_le_mono.
  rewrite<- add_0_l at 1.
  rewrite add_comm.
  apply add_le_mono_l.
  order_pos_log.
Qed.

End N.

(* Intuitively: This lemma is true because the change in the base
   means fewer or at least no more multiplications will be necessary.

   n ^ (log n a) <= m ^ (log n a)
*)
Lemma log_base_mono:
  forall n m a : t, n > 1 -> m > 1 -> n <= m -> a > 0 -> log m a <= log n a.
Proof.
  intros n m a Hn Hm Hnm Ha.
  apply log_le_pown.
  exact Hn.
  exact Ha.
  assert (Hspecm := log_spec m a Hm Ha).
  assert (Hspecn := log_spec n a Hn Ha).
  apply (le_trans _ (m ^ log m a) _).
  apply pow_le_mono_l.
  apply conj.
  order_pos.
  exact Hnm.
  easy.
Qed.

End NLogProp.

(* Local Variables: *)
(* coq-prog-name: "/usr/local/bin/coqtop" *)
(* coq-load-path: ("/Users/Fred/Documents/proofs/scales") *)
(* End: *)
