Require Export RelationClasses Morphisms Utf8.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Coquelicot Require Import Hierarchy Markov Rcomplements Rbar Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive AutoDerive.
Require Import RealsExt.
Require Export Reals.
Require Import Coqlib.
Require Import Psatz.
Import Rbar.

Definition strict_increasing := λ f : R → R, ∀ x y : R, x < y → f x < f y.

Lemma strict_increasing_increasing f :
  strict_increasing f →
  increasing f.
Proof.
  rewrite /strict_increasing/increasing. intros Hinc x y Hle.
  destruct Hle.
  { left. apply Hinc; eauto. }
  { subst. nra. }
Qed.

Definition logit u := ln (u / (1 - u)).
Definition logit_inv u := 1 / (1 + exp(-u)).

(** Lower Bounded Scalar *)

Definition unconstrain_lb a x := ln (x - a).
Definition constrain_lb a x := exp x + a.
Definition deriv_constrain_lb (a: R) x := exp x.

Definition constrain_lb_lim (a: R) (x : Rbar) : Rbar :=
  match x with
  | m_infty => a
  | Finite x => constrain_lb a x
  | p_infty => p_infty
  end.

Lemma constrain_lb_lim_right_correct a x :
  x <> p_infty ->
  is_right_lim (constrain_lb a) x (constrain_lb_lim a x).
Proof.
  destruct x => /=.
  - intros _. apply is_lim_right_lim; first congruence.
    { apply is_lim_continuity'.
      apply: continuous_plus.
      * apply ElemFct.continuous_exp.
      * apply continuous_const.
    }
  - intros ?. congruence.
  - intros _.
    replace a with (0 + a) at 2; last nra.
    rewrite /constrain_lb.
    apply (is_right_lim_plus' exp (λ _, a)).
    * apply is_lim_right_lim; first congruence.
      apply ElemFct.is_lim_exp_m.
    * apply is_right_lim_const; congruence.
Qed.

Lemma constrain_lb_lim_left_correct a x :
  x <> m_infty ->
  is_left_lim (constrain_lb a) x (constrain_lb_lim a x).
Proof.
  destruct x => /=.
  - intros _. apply is_lim_left_lim; first congruence.
    { apply is_lim_continuity'.
      apply: continuous_plus.
      * apply ElemFct.continuous_exp.
      * apply continuous_const.
    }
  - intros _.
    rewrite /constrain_lb.
    apply (is_left_lim_plus exp (λ _, a) p_infty p_infty a p_infty).
    * apply is_lim_left_lim; first congruence.
      apply ElemFct.is_lim_exp_p.
    * apply is_left_lim_const; congruence.
    * econstructor.
  - intros ?. congruence.
Qed.

Lemma deriv_constrain_lb_correct a x :
  is_derive (constrain_lb a) x (deriv_constrain_lb a x).
Proof.
  rewrite /constrain_lb/deriv_constrain_lb.
  auto_derive; auto. nra.
Qed.

Lemma deriv_constrain_lb_pos a x:
  0 < deriv_constrain_lb a x.
Proof. rewrite /deriv_constrain_lb. apply exp_pos. Qed.

Lemma constrain_lb_strict_increasing a :
  strict_increasing (constrain_lb a).
Proof.
  rewrite /constrain_lb.
  intros x y Hle.
  apply Rplus_lt_compat_r.
  apply exp_increasing; auto.
Qed.

Lemma constrain_lb_increasing a :
  increasing (constrain_lb a).
Proof.
  apply strict_increasing_increasing, constrain_lb_strict_increasing.
Qed.

Lemma constrain_lb_inv :
  forall a x, a < x -> constrain_lb a (unconstrain_lb a x) = x.
Proof.
  intros a x Hrange. rewrite /constrain_lb/unconstrain_lb.
  rewrite exp_ln; nra.
Qed.

Lemma unconstrain_lb_inv :
  forall a x, unconstrain_lb a (constrain_lb a x) = x.
Proof.
  intros a x. rewrite /constrain_lb/unconstrain_lb.
  rewrite -{2}(ln_exp (x)). f_equal. ring.
Qed.

Lemma constrain_lb_spec_strict a x :
  a < constrain_lb a x.
Proof.
  rewrite /constrain_lb. cut (0 < exp x); first by nra.
  apply exp_pos.
Qed.

Lemma constrain_lb_spec a x :
  a <= constrain_lb a x.
Proof. left. apply constrain_lb_spec_strict. Qed.

(* Upper bounded scalar *)

(* NOTE: stan uses lb (b - x) instead, but that is not monotone increasing, and instead is monotone decreasing.
   This is a slight incompatiblity, but it should not matter.
 *)

Definition unconstrain_ub b x := - ln (b - x).
Definition constrain_ub b x := b - exp (- x).
Definition deriv_constrain_ub (b: R) x := exp (- x).

Definition constrain_ub_lim (a: R) (x : Rbar) : Rbar :=
  match x with
  | m_infty => m_infty
  | Finite x => constrain_ub a x
  | p_infty => a
  end.

Lemma continuous_constrain_ub a r :
  continuous (constrain_ub a) r.
Proof.
  apply: continuous_plus.
  * apply continuous_const.
  * apply: continuous_opp. apply continuous_comp.
    { apply: continuous_opp. apply continuous_id. }
    apply ElemFct.continuous_exp.
Qed.

Lemma constrain_ub_lim_right_correct a x :
  x <> p_infty ->
  is_right_lim (constrain_ub a) x (constrain_ub_lim a x).
Proof.
  destruct x => /=.
  - intros _. apply is_lim_right_lim; first congruence.
    { apply is_lim_continuity', continuous_constrain_ub. }
  - intros ?. congruence.
  - intros _.
    replace a with (a - 0) at 2; last nra.
    rewrite /constrain_ub.
    rewrite /Rminus.
    apply (is_right_lim_plus (λ _, a) (λ x, - exp (- x)) m_infty a m_infty m_infty).
    * apply is_right_lim_const. congruence.
    * apply is_lim_right_lim; first congruence.
      replace (m_infty) with (Rbar_opp p_infty); auto.
      apply is_lim_opp; simpl.
      eapply is_lim_comp.
      { apply ElemFct.is_lim_exp_p. }
      { replace (p_infty) with (Rbar_opp m_infty); auto. apply: is_lim_opp.
        apply is_lim_id. }
      { simpl => //=. exists 0. intros ??. congruence. }
      rewrite //=.
Qed.

Lemma constrain_ub_lim_left_correct a x :
  x <> m_infty ->
  is_left_lim (constrain_ub a) x (constrain_ub_lim a x).
Proof.
  destruct x => /=.
  - intros _. apply is_lim_left_lim; first congruence.
    { apply is_lim_continuity', continuous_constrain_ub. }
  - intros _.
    rewrite /constrain_ub.
    replace a with (a - 0) at 1; last nra.
    rewrite /Rminus.
    apply (is_left_lim_plus (λ _, a) (λ x, - exp (- x)) p_infty a 0 (a - 0)).
    * apply is_left_lim_const; congruence.
    * apply is_lim_left_lim; first congruence.
      replace (Finite 0) with (Rbar_opp 0); last (rewrite //=; f_equal; nra).
      apply is_lim_opp; simpl.
      eapply is_lim_comp.
      { apply ElemFct.is_lim_exp_m. }
      { replace (m_infty) with (Rbar_opp p_infty); auto. apply: is_lim_opp.
        apply is_lim_id. }
      { simpl => //=. exists 0. intros ??. congruence. }
      rewrite /Rminus.
      rewrite /is_Rbar_plus/=. do 2 f_equal. nra.
  - intros ?. congruence.
Qed.

Lemma deriv_constrain_ub_correct b x :
  is_derive (constrain_ub b) x (deriv_constrain_ub b x).
Proof.
  rewrite /constrain_ub/deriv_constrain_ub.
  auto_derive; auto. nra.
Qed.

Lemma deriv_constrain_ub_pos b x:
  0 < deriv_constrain_lb b x.
Proof. rewrite /deriv_constrain_ub. apply exp_pos. Qed.

Lemma constrain_ub_strict_increasing a :
  strict_increasing (constrain_ub a).
Proof.
  rewrite /constrain_ub.
  intros x y Hle.
  apply Rplus_lt_compat_l.
  cut (exp (-y) < exp (- x)); first by nra.
  apply exp_increasing; auto.
Qed.

Lemma constrain_ub_increasing a :
  increasing (constrain_ub a).
Proof.
  apply strict_increasing_increasing, constrain_ub_strict_increasing.
Qed.

Lemma constrain_ub_inv :
  forall b x, x < b -> constrain_ub b (unconstrain_ub b x) = x.
Proof.
  intros b x Hrange. rewrite /constrain_ub/unconstrain_ub.
  rewrite Ropp_involutive.
  rewrite exp_ln; nra.
Qed.

Lemma unconstrain_ub_inv :
  forall b x, unconstrain_ub b (constrain_ub b x) = x.
Proof.
  intros b x. rewrite /constrain_ub/unconstrain_ub.
  transitivity (- ln (exp (-x))).
  { do 2 f_equal. ring. }
  rewrite ln_exp. nra.
Qed.

Lemma constrain_ub_spec_strict b x :
  constrain_ub b x < b.
Proof.
  rewrite /constrain_ub. cut (0 < exp (- x)); first by nra.
  apply exp_pos.
Qed.

Lemma constrain_ub_spec b x :
   constrain_ub b x <= b.
Proof. left. apply constrain_ub_spec_strict. Qed.

(* Lower and upper bounded scalar *)

Definition unconstrain_lb_ub a b x :=
  logit ((x - a) / (b - a)).
Definition constrain_lb_ub a b x :=
  a + (b - a) * logit_inv x.
Definition deriv_constrain_lb_ub a b x :=
  (b - a) * logit_inv x * (1 - logit_inv x).

Definition constrain_lb_ub_lim (a b: R) (x : Rbar) : Rbar :=
  match x with
  | m_infty => a
  | Finite x => constrain_lb_ub a b x
  | p_infty => b
  end.

Lemma deriv_constrain_lb_ub_correct a b x:
  is_derive (constrain_lb_ub a b) x (deriv_constrain_lb_ub a b x).
Proof.
  rewrite /constrain_lb_ub/deriv_constrain_lb_ub/logit_inv.
  assert (1 + exp (- x) ≠ 0).
  { specialize (exp_pos (- x)). nra. }
  auto_derive; auto. field; auto.
Qed.

Lemma continuous_constrain_lb_ub a b r :
  continuous (constrain_lb_ub a b) r.
Proof. apply: ex_derive_continuous. eexists. eapply deriv_constrain_lb_ub_correct. Qed.

Lemma is_lim_logit_inv_m :
  is_lim logit_inv m_infty 0.
Proof.
  rewrite /logit_inv.
  replace (Finite 0) with (Rbar_div 1 (Rbar_plus 1 p_infty)); last first.
  { rewrite //=. f_equal. field. }
  apply: is_lim_div.
  { apply is_lim_const. }
  { apply: is_lim_plus.
    { apply is_lim_const. }
    { eapply is_lim_comp.
      { apply ElemFct.is_lim_exp_p. }
      { replace (p_infty) with (Rbar_opp m_infty); auto. apply: is_lim_opp.
        apply is_lim_id. }
      { simpl => //=. exists 0. intros ??. congruence. } }
    { rewrite //=. }
  }
  { rewrite //=. }
  { rewrite //=. }
Qed.

Lemma is_lim_logit_inv_p :
  is_lim logit_inv p_infty 1.
Proof.
  rewrite /logit_inv.
  replace (Finite 1) with (Rbar_div 1 (Rbar_plus 1 0)); last first.
  { rewrite //=. f_equal. field. }
  apply: is_lim_div.
  { apply is_lim_const. }
  { apply: is_lim_plus.
    { apply is_lim_const. }
    { eapply is_lim_comp.
      { apply ElemFct.is_lim_exp_m. }
      { replace (m_infty) with (Rbar_opp p_infty); auto. apply: is_lim_opp.
        apply is_lim_id. }
      { simpl => //=. exists 0. intros ??. congruence. } }
    { rewrite //=. }
  }
  { rewrite //=. inversion 1. nra. }
  { rewrite //=. }
Qed.

Lemma constrain_lb_ub_lim_right_correct a b x :
  x <> p_infty ->
  is_right_lim (constrain_lb_ub a b) x (constrain_lb_ub_lim a b x).
Proof.
  destruct x => /=.
  - intros _. apply is_lim_right_lim; first congruence.
    { apply is_lim_continuity', continuous_constrain_lb_ub. }
  - intros ?. congruence.
  - intros _.
    replace a with (a + 0) at 2; last nra.
    apply (is_right_lim_plus (λ _, a) (λ x, (b - a) * logit_inv x) m_infty a 0).
    { apply is_right_lim_const. congruence. }
    { apply is_lim_right_lim; first congruence.
      replace (Finite 0) with (Rbar_mult (b - a) 0); last first.
      { rewrite /=. f_equal. field. }
      apply is_lim_mult.
      { apply is_lim_const. }
      { apply is_lim_logit_inv_m. }
      { rewrite //=. } }
    { rewrite //=. }
Qed.

Lemma constrain_lb_ub_lim_left_correct a b x :
  x <> m_infty ->
  is_left_lim (constrain_lb_ub a b) x (constrain_lb_ub_lim a b x).
Proof.
  destruct x => /=.
  - intros _. apply is_lim_left_lim; first congruence.
    { apply is_lim_continuity', continuous_constrain_lb_ub. }
  - intros _.
    replace b with (a + ((b - a) * 1)) at 2; last nra.
    apply (is_left_lim_plus (λ _, a) _ p_infty a (Rbar_mult (b - a) 1)).
    { apply is_left_lim_const; congruence. }
    { apply is_lim_left_lim; first congruence.
      apply is_lim_mult.
      { apply is_lim_const. }
      { apply is_lim_logit_inv_p. }
      { rewrite //=. } }
    { rewrite //=. }
  - intros ?. congruence.
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

Lemma constrain_lb_ub_strict_increasing a b :
  a < b ->
  strict_increasing (constrain_lb_ub a b).
Proof.
  rewrite /constrain_lb_ub.
  intros Hrange x y Hle. rewrite /logit_inv.
  apply Rplus_lt_compat_l.
  apply Rmult_lt_compat_l; first nra.
  apply Rmult_lt_compat_l; first nra.
  apply Rinv_lt_contravar.
  { specialize (exp_pos (- y)); specialize (exp_pos (- x)); nra. }
  apply Rplus_lt_compat_l.
  apply exp_increasing; nra.
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

Lemma logit_inv_spec2 x :
  logit (logit_inv x) = x.
Proof.
  intros.
  rewrite /logit_inv/logit. rewrite -[a in _ = a](ln_exp x).
  f_equal. field_simplify.
  { rewrite exp_Ropp. field. specialize (exp_pos x); nra. }
  specialize (exp_pos (-x)). nra.
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

Lemma unconstrain_lb_ub_inv :
  forall a b x, a ≠ b -> unconstrain_lb_ub a b (constrain_lb_ub a b x) = x.
Proof.
  intros a b x. rewrite /constrain_lb_ub/unconstrain_lb_ub.
  transitivity (logit (logit_inv x)).
  { f_equal. field. nra. }
  rewrite logit_inv_spec2 //.
Qed.

Lemma constrain_lb_ub_spec_strict a b x :
  a < b ->
  a < constrain_lb_ub a b x < b.
Proof.
  rewrite /constrain_lb_ub. specialize (logit_inv_range x); nra.
Qed.

Lemma constrain_lb_ub_spec a b x :
  a <= b ->
  a <= constrain_lb_ub a b x <= b.
Proof.
  rewrite /constrain_lb_ub. specialize (logit_inv_range x); nra.
Qed.
