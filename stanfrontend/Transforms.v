Require Export RelationClasses Morphisms Utf8.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Coquelicot Require Import Hierarchy Markov Rcomplements Rbar Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive AutoDerive.
Require Import RealsExt.
Require ClassicalEpsilon.
Require Import Reals.
Require Import Coqlib.
Require Import Psatz.
Require Import Program.Basics.
Import Rbar.

Definition logit u := ln (u / (1 - u)).
Definition logit_inv u := 1 / (1 + exp(-u)).
Definition unconstrain_lb_ub a b x :=
  logit ((x - a) / (b - a)).
Definition constrain_lb_ub a b x :=
  a + (b - a) * logit_inv x.
Definition deriv_constrain_lb_ub a b x :=
  (b - a) * logit_inv x * (1 - logit_inv x).

Lemma deriv_constrain_lb_ub_correct a b x:
  is_derive (constrain_lb_ub a b) x (deriv_constrain_lb_ub a b x).
Proof.
  rewrite /constrain_lb_ub/deriv_constrain_lb_ub/logit_inv.
  assert (1 + exp (- x) ≠ 0).
  { specialize (exp_pos (- x)). nra. }
  auto_derive; auto. field; auto.
Qed.

Lemma logit_inv_range x :
   0 < logit_inv x < 1.
Proof.
  rewrite /logit_inv; specialize (exp_pos (-x)); intros; split.
  - apply Rdiv_lt_0_compat; nra.
  - apply Rlt_div_l; nra.
Qed.

Lemma deriv_constrain_lb_ub_pos a b x:
  a < b ->
  0 < deriv_constrain_lb_ub a b x.
Proof.
  rewrite /deriv_constrain_lb_ub.
  specialize (logit_inv_range x) => ??.
  apply Rmult_lt_0_compat; last by nra.
  apply Rmult_lt_0_compat; nra.
Qed.

Lemma constrain_lb_ub_increasing a b :
  a <= b ->
  increasing (constrain_lb_ub a b).
Proof.
  rewrite /constrain_lb_ub.
  intros Hrange x y Hle. rewrite /logit_inv.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l; first nra.
  apply Rmult_le_compat_l; first nra.
  apply Rinv_le_contravar.
  { specialize (exp_pos (- y)). nra. }
  apply Rplus_le_compat_l.
  destruct Hle; last by (subst; nra).
  left.
  apply exp_increasing; nra.
Qed.

Lemma logit_inv_spec x :
  0 < x < 1 -> logit_inv (logit x) = x.
Proof.
  intros.
  rewrite /logit_inv/logit. rewrite exp_Ropp. rewrite exp_ln.
  { field; nra. }
  { apply Rdiv_lt_0_compat; nra. }
Qed.

Lemma constrain_lb_ub_inv :
  forall a b x, a < x < b -> constrain_lb_ub a b (unconstrain_lb_ub a b x) = x.
Proof.
  intros a b x Hrange. rewrite /constrain_lb_ub/unconstrain_lb_ub.
  rewrite logit_inv_spec.
  { field. nra. }
  split.
  { apply Rdiv_lt_0_compat; nra. }
  { apply Rlt_div_l; nra. }
Qed.

Lemma constrain_lb_ub_spec a b x :
  a <= b ->
  a <= constrain_lb_ub a b x <= b.
Proof.
  rewrite /constrain_lb_ub. specialize (logit_inv_range x); nra.
Qed.

