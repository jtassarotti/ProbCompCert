Require Export RelationClasses Morphisms Utf8.
From mathcomp Require Import ssreflect ssrbool eqtype.
From Coquelicot Require Import Hierarchy Markov Rcomplements Rbar Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive AutoDerive.

Require ClassicalEpsilon.
Require Import Reals.
Require Import Coqlib.
Require Import Psatz.
Require Import Program.Basics.
Require Import RealsExt Transforms.
Import Rbar.

(** Left/Right limits of integral boundary *)

Lemma is_RInt_upper_bound_left_lim a b f v :
  Rlt a b ->
  is_RInt f a b v ->
  is_left_lim (RInt f a) b (RInt f a b).
Proof.
  intros Hlt His.
  unfold is_left_lim. split; first done.
  unfold filterlim, filter_le, filtermap, Rbar_at_left, within, Rbar_locally, locally. intros P HP.
  destruct HP as (eps&Heps).
  cut (∃ eps' : posreal, ∀ y, ball b eps' y -> Rbar_lt y b -> ball (RInt f a b) eps (RInt f a y)).
  { intros (eps'&Heps'). exists eps'. intros y Hball Hbar. apply Heps, Heps'; auto. }
  edestruct (ex_RInt_ub f a b) as (ub&Hub); first (econstructor; eauto).
  assert (∀ t, a <= t <= b -> Rabs (RInt f t b) <= (b - t) * ub).
  { intros t Hle. apply abs_RInt_le_const; intuition.
    { apply: ex_RInt_Chasles_2.
      { split; eassumption. }
      econstructor; eauto. }
    apply Hub. split.
    { rewrite Rmin_left; nra. }
    { rewrite Rmax_right; nra. }
  }
  assert (0 <= ub).
  { specialize (Hub a). transitivity (norm (f a)).
    { apply norm_ge_0. }
    { apply Hub. rewrite Rmin_left ?Rmax_right; nra. }
  }
  assert (Heps': 0 < eps / (ub + 1)).
  { apply Rdiv_lt_0_compat.
    { destruct eps; auto. }
    { nra. }
  }
  set (eps' := (mkposreal _ Heps')).
  edestruct (eps_squeeze_between a b eps') as (eps''&Hsmaller&Heps''); auto.
  exists eps''.
  rewrite /ball/=/AbsRing_ball/=/abs/=/minus/plus/opp/=.
  intros y Hball Hlty.
  assert (a <= y).
  { apply Heps''. auto. }
  rewrite -(RInt_Chasles f a y b); swap 1 3.
  { eapply ex_RInt_Chasles_2; last first.
    { econstructor; eauto. }
    split; nra. }
  { eapply ex_RInt_Chasles_1; last first.
    { econstructor; eauto. }
    split; nra. }
  eapply (Rle_lt_trans _ (Rabs (RInt f y b))).
  { right. rewrite -Rabs_Ropp. f_equal. rewrite /plus//=. nra. }
  eapply (Rle_lt_trans); first (eapply H; nra).
  rewrite Rabs_left in Hball; last first.
  { nra. }
  assert (b - y < eps'' ) by nra.
  apply (Rle_lt_trans _ (eps' * ub)).
  { apply Rmult_le_compat_r; nra. }
  rewrite /eps' /=. rewrite /Rdiv. rewrite Rmult_assoc.
  apply (Rlt_le_trans _ (eps * 1)); last nra.
  apply Rmult_lt_compat_l; first by (destruct eps).
  rewrite Rmult_comm. apply (Rdiv_lt_1 ub (ub + 1)); nra.
Qed.

Lemma is_RInt_lower_bound_right_lim a b f v :
  Rlt a b ->
  is_RInt f a b v ->
  is_right_lim (λ x, RInt f x b) a (RInt f a b).
Proof.
  intros Hlt His.
  unfold is_right_lim. split; first done.
  unfold filterlim, filter_le, filtermap, Rbar_at_right, within, Rbar_locally, locally. intros P HP.
  destruct HP as (eps&Heps).
  cut (∃ eps' : posreal, ∀ y, ball a eps' y -> Rbar_lt a y -> ball (RInt f a b) eps (RInt f y b)).
  { intros (eps'&Heps'). exists eps'. intros y Hball Hbar. apply Heps, Heps'; auto. }
  edestruct (ex_RInt_ub f a b) as (ub&Hub); first (econstructor; eauto).
  assert (∀ t, a <= t <= b -> Rabs (RInt f a t) <= (t - a) * ub).
  { intros t Hle. apply abs_RInt_le_const; intuition.
    { apply: ex_RInt_Chasles_1.
      { split; eassumption. }
      econstructor; eauto. }
    apply Hub. split.
    { rewrite Rmin_left; nra. }
    { rewrite Rmax_right; nra. }
  }
  assert (0 <= ub).
  { specialize (Hub a). transitivity (norm (f a)).
    { apply norm_ge_0. }
    { apply Hub. rewrite Rmin_left ?Rmax_right; nra. }
  }
  assert (Heps': 0 < eps / (ub + 1)).
  { apply Rdiv_lt_0_compat.
    { destruct eps; auto. }
    { nra. }
  }
  set (eps' := (mkposreal _ Heps')).
  edestruct (eps_squeeze_between' a b eps') as (eps''&Hsmaller&Heps''); auto.
  exists eps''.
  rewrite /ball/=/AbsRing_ball/=/abs/=/minus/plus/opp/=.
  intros y Hball Hlty.
  assert (y <= b).
  { apply Heps''. auto. }
  rewrite -(RInt_Chasles f a y b); swap 1 3.
  { eapply ex_RInt_Chasles_2; last first.
    { econstructor; eauto. }
    split; nra. }
  { eapply ex_RInt_Chasles_1; last first.
    { econstructor; eauto. }
    split; nra. }
  eapply (Rle_lt_trans _ (Rabs (RInt f a y))).
  { right. rewrite -Rabs_Ropp. f_equal. rewrite /plus//=. nra. }
  eapply (Rle_lt_trans); first (eapply H; nra).
  rewrite Rabs_right in Hball; last first.
  { nra. }
  assert (y - a < eps'' ) by nra.
  apply (Rle_lt_trans _ (eps' * ub)).
  { apply Rmult_le_compat_r; nra. }
  rewrite /eps' /=. rewrite /Rdiv. rewrite Rmult_assoc.
  apply (Rlt_le_trans _ (eps * 1)); last nra.
  apply Rmult_lt_compat_l; first by (destruct eps).
  rewrite Rmult_comm. apply (Rdiv_lt_1 ub (ub + 1)); nra.
Qed.

Lemma is_RInt_comp' : ∀ (f : R → R) (g dg : R → R) (a b : R),
    a <= b →
    (∀ x : R, a <= x <= b → continuous f (g x)) →
    (∀ x : R, a <= x <= b → is_derive g x (dg x) ∧ continuous dg x) →
    is_RInt (λ y : R, scal (dg y) (f (g y))) a b (RInt f (g a) (g b)).
Proof.
  intros f g dg a b Hle Hcont Hdiff. apply: is_RInt_comp.
  - intros x. rewrite Rmin_left // Rmax_right //. apply Hcont.
  - intros x. rewrite Rmin_left // Rmax_right //. apply Hdiff.
Qed.

Lemma ex_RInt_comp' : ∀ (f : R → R) (g dg : R → R) (a b : R),
    a <= b →
    (∀ x : R, a <= x <= b → continuous f (g x)) →
    (∀ x : R, a <= x <= b → is_derive g x (dg x) ∧ continuous dg x) →
    ex_RInt (λ y : R, scal (dg y) (f (g y))) a b.
Proof.
  intros f g dg a b Hle Hcont Hdiff. eexists; apply: is_RInt_comp'; auto.
Qed.

Lemma RInt_comp' : ∀ (f : R → R) (g dg : R → R) (a b : R),
    a <= b →
    (∀ x : R, a <= x <= b → continuous f (g x)) →
    (∀ x : R, a <= x <= b → is_derive g x (dg x) ∧ continuous dg x) →
    RInt (λ y : R, scal (dg y) (f (g y))) a b = RInt f (g a) (g b).
Proof.
  intros f g dg a b Hle Hcont Hdiff. apply: RInt_comp.
  - intros x. rewrite Rmin_left // Rmax_right //. apply Hcont.
  - intros x. rewrite Rmin_left // Rmax_right //. apply Hdiff.
Qed.

Lemma Rbar_at_left_interval a b (P: Rbar -> Prop) :
  Rbar_lt a b ->
  (∀ x, Rbar_lt a x -> Rbar_lt x b -> P x) ->
  Rbar_at_left b P.
Proof.
  intros Hlt HP. unfold Rbar_at_left, within.
  apply open_Rbar_gt' in Hlt. move:Hlt. apply filter_imp.
  intros. apply HP; auto.
Qed.

Lemma Rbar_at_right_interval a b (P: Rbar -> Prop) :
  Rbar_lt a b ->
  (∀ x, Rbar_lt a x -> Rbar_lt x b -> P x) ->
  Rbar_at_right a P.
Proof.
  intros Hlt HP. unfold Rbar_at_right, within.
  apply open_Rbar_lt' in Hlt. move:Hlt. apply filter_imp.
  intros. apply HP; auto.
Qed.

Lemma ball_interval_lb r eps x :
  ball r eps x ->
  r - eps < x.
Proof.
  rewrite /ball/=/AbsRing_ball/abs/=/minus/plus/opp//=. apply Rabs_case; nra.
Qed.

Lemma ball_interval_ub r eps x :
  ball r eps x ->
  x < r + eps.
Proof.
  rewrite /ball/=/AbsRing_ball/abs/=/minus/plus/opp//=. apply Rabs_case; nra.
Qed.

Lemma not_Rbar_at_left b P :
  ¬ Rbar_at_left b P →
  match b with
  | Finite r => ∀ eps : posreal, ∃ x, r - eps < x < r ∧ ¬ P x
  | p_infty => ∀ M, ∃ x, M < x ∧ ¬ P x
  | m_infty => True
  end.
Proof.
  intros Hneg.
  destruct b; auto.
  - intros eps. unfold Rbar_at_left, within, Rbar_locally, locally in Hneg.
    specialize (Classical_Pred_Type.not_ex_all_not _ _ Hneg eps) => /= Heps.
    apply Classical_Pred_Type.not_all_ex_not in Heps.
    destruct Heps as (x&Hx).
    assert (Hx': ¬ ((ball r eps x ∧ x < r) → P x)) by intuition.
    eapply Classical_Prop.not_imply_elim in Hx'.
    exists x.
    split; last first.
    { eapply Classical_Prop.not_imply_elim2 in Hx; eauto. }
    intuition.
    apply ball_interval_lb; auto.
  - intros M. unfold Rbar_at_left, within, Rbar_locally, locally in Hneg.
    specialize (Classical_Pred_Type.not_ex_all_not _ _ Hneg M) => /= Heps.
    apply Classical_Pred_Type.not_all_ex_not in Heps.
    destruct Heps as (x&Hx).
    assert (Hx': ¬ (M < x → P x)) by intuition.
    eapply Classical_Prop.not_imply_elim in Hx'.
    exists x.
    split; last first.
    { eapply Classical_Prop.not_imply_elim2 in Hx; eauto. }
    auto.
Qed.

Lemma not_Rbar_at_right b P :
  ¬ Rbar_at_right b P →
  match b with
  | Finite r => ∀ eps : posreal, ∃ x, r < x < r + eps ∧ ¬ P x
  | p_infty => True
  | m_infty =>  ∀ M, ∃ x, x < M ∧ ¬ P x
  end.
Proof.
  intros Hneg.
  destruct b; auto.
  - intros eps. unfold Rbar_at_right, within, Rbar_locally, locally in Hneg.
    specialize (Classical_Pred_Type.not_ex_all_not _ _ Hneg eps) => /= Heps.
    apply Classical_Pred_Type.not_all_ex_not in Heps.
    destruct Heps as (x&Hx).
    assert (Hx': ¬ ((ball r eps x ∧ r < x) → P x)) by intuition.
    eapply Classical_Prop.not_imply_elim in Hx'.
    exists x.
    split; last first.
    { eapply Classical_Prop.not_imply_elim2 in Hx; eauto. }
    intuition.
    apply ball_interval_ub; auto.
  - intros M. unfold Rbar_at_right, within, Rbar_locally, locally in Hneg.
    specialize (Classical_Pred_Type.not_ex_all_not _ _ Hneg M) => /= Heps.
    apply Classical_Pred_Type.not_all_ex_not in Heps.
    destruct Heps as (x&Hx).
    assert (Hx': ¬ (x < M → P x)) by intuition.
    eapply Classical_Prop.not_imply_elim in Hx'.
    exists x.
    split; last first.
    { eapply Classical_Prop.not_imply_elim2 in Hx; eauto. }
    auto.
Qed.

Lemma interval_inhabited (x y : R) : x < y -> ∃ z, x < z < y.
Proof.
  intros.
  edestruct (boule_of_interval x y) as (s&(r&Heq1&Heq2)); auto.
  exists s. nra.
Qed.

Lemma Rbar_interval_inhabited (a b : Rbar) :
  Rbar_lt a b -> ∃ (c : R), Rbar_lt a c /\ Rbar_lt c b.
Proof.
  destruct a as [r | | ].
  - destruct b as [ r' | |].
    * simpl. apply interval_inhabited.
    * intros _. exists (r + 1). simpl; split; auto; first nra.
    * simpl; intuition.
  - inversion 1.
  - destruct b as [ r' | | ].
    * intros _. exists (r' - 1). simpl; split; auto; last nra.
    * intros _. exists 0; simpl; done.
    * inversion 1.
Qed.

Lemma Rbar_at_left_witness (r: R) (eps: posreal) P:
  Rbar_at_left r P -> ∃ x, r - eps < x < r ∧ P x.
Proof.
  unfold Rbar_at_left, within, Rbar_locally, locally.
  intros Hex. destruct Hex as (eps'&Heps').
  set (lb := r - Rmin eps eps').
  edestruct (interval_inhabited lb r) as (x&Hin).
  { rewrite /lb. apply Rmin_case; destruct eps, eps' => /=; nra. }
  exists x. split.
  { move: Hin. rewrite /lb. apply Rmin_case_strong; destruct eps, eps' => /=; nra. }
  apply Heps'; last by intuition.
  rewrite /ball/=/AbsRing_ball/abs/=/minus/plus/opp//=.
  { move: Hin. rewrite /lb. apply Rabs_case; apply Rmin_case_strong; destruct eps, eps' => /=; nra. }
Qed.

Lemma Rbar_at_left_witness_above (r: R) y P:
  Rbar_at_left r P -> y < r -> ∃ x, y < x < r ∧ P x.
Proof.
  intros. assert (Hpos: 0 < r - y) by nra.
  edestruct (Rbar_at_left_witness r (mkposreal _ Hpos) P) as (x&?&HP); auto.
  exists x. split; auto.
  simpl in H1. nra.
Qed.

Lemma Rbar_at_left_witness_above_p_infty y P:
  Rbar_at_left p_infty P -> ∃ x, y < x ∧ P x.
Proof.
  unfold Rbar_at_left, within, Rbar_locally.
  intros HM. destruct HM as (M&HM). exists (Rmax (M + 1) (y + 1)).
  split.
  - apply (Rlt_le_trans _ (y + 1)); first nra.
    apply Rmax_r.
  - apply HM; simpl; auto.
  - apply (Rlt_le_trans _ (M + 1)); first nra.
    apply Rmax_l.
Qed.

Lemma Rbar_at_left_strict_monotone (t : R) (b : Rbar) g glim :
  Rbar_lt t b →
  (∀ (x y : R), Rbar_lt t x /\ x < y → Rbar_lt y b → g x < g y) →
  is_left_lim g b glim ->
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glim).
Proof.
  unfold is_left_lim.
  intros Hltb Ht (Hnm&Hlim).
  apply Classical_Prop.NNPP. intros Hneg%not_Rbar_at_left.
  destruct b; try congruence.
  - unfold filterlim, filter_le, filtermap in Hlim.
    assert (Hpos: 0 < r - t).
    { simpl in Hltb. nra. }
    set (eps' := mkposreal _ Hpos).
    specialize (Hneg eps').
    assert (∃ x : R, (r - eps' < x ∧ x < r) ∧ Rbar_lt glim (g x)) as (x&Hrange&r0).
    {
      destruct Hneg as (x&Hrange&Hnlt).
      apply Rbar_not_lt_le in Hnlt.
      apply Rbar_le_lt_or_eq_dec in Hnlt.
      destruct Hnlt as [Hlt|Heq].
      { exists x. split; eauto. }
      destruct (interval_inhabited x r) as (x'&Hx'1&Hx'2); first nra.
      exists x'.
      split; first nra.
      rewrite Heq. simpl. apply Ht; auto; split; try nra.
      move: Hrange. rewrite /eps' /=. nra.
    }
    apply open_Rbar_lt' in r0. apply Hlim in r0.
    eapply (Rbar_at_left_witness_above r x) in r0; try (intuition eauto; done).
    destruct r0 as (y&Hrange'&Hlt).
    simpl in Hlt. apply Rlt_not_le in Hlt.
    apply Hlt. left. apply Ht; simpl; simpl in Hltb; try nra.
    split; last by intuition.
    move: Hrange. rewrite /eps' /=. nra.
  - unfold filterlim, filter_le, filtermap in Hlim.
    specialize (Hneg t).
    assert (∃ x : R, t < x ∧ Rbar_lt glim (g x)) as (x&Hrange&r0).
    {
      destruct Hneg as (x&Hrange&Hnlt).
      apply Rbar_not_lt_le in Hnlt.
      apply Rbar_le_lt_or_eq_dec in Hnlt.
      destruct Hnlt as [Hlt|Heq].
      { exists x. split; eauto. }
      exists (x + 1).
      split; first nra.
      rewrite Heq. simpl. apply Ht; auto; split; simpl; try nra.
    }
    apply open_Rbar_lt' in r0. apply Hlim in r0.
    eapply (Rbar_at_left_witness_above_p_infty x) in r0; try (intuition eauto; done).
    destruct r0 as (y&Hrange'&Hlt).
    simpl in Hlt. apply Rlt_not_le in Hlt.
    apply Hlt. left. apply Ht; simpl; simpl in Hltb; try nra.
Qed.

Lemma Rbar_at_left_strict_monotone' (t : Rbar) (b : Rbar) g glim :
  Rbar_lt t b →
  (∀ (x y : R), Rbar_lt t x /\ x < y → Rbar_lt y b → g x < g y) →
  is_left_lim g b glim ->
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glim).
Proof.
  intros Hlt Hmono Hlim.
  destruct t.
  - eapply Rbar_at_left_strict_monotone; eauto.
  - inversion Hlt.
  - destruct b as [r' | |].
    { eapply (Rbar_at_left_strict_monotone (Rmin 0 (r' - 1))); eauto.
      { simpl. apply Rmin_case_strong; nra. }
      { intros. apply Hmono; auto. split; intuition auto. }
    }
    { eapply (Rbar_at_left_strict_monotone 0); eauto.
      { intros. apply Hmono; auto. split; intuition auto. }
    }
    { inversion Hlt. }
Qed.

Lemma Rbar_at_right_witness (r: R) (eps: posreal) P:
  Rbar_at_right r P -> ∃ x, r < x < r + eps ∧ P x.
Proof.
  unfold Rbar_at_right, within, Rbar_locally, locally.
  intros Hex. destruct Hex as (eps'&Heps').
  set (lb := r + Rmin eps eps').
  edestruct (interval_inhabited r lb) as (x&Hin).
  { rewrite /lb. apply Rmin_case; destruct eps, eps' => /=; nra. }
  exists x. split.
  { move: Hin. rewrite /lb. apply Rmin_case_strong; destruct eps, eps' => /=; nra. }
  apply Heps'; last by intuition.
  rewrite /ball/=/AbsRing_ball/abs/=/minus/plus/opp//=.
  { move: Hin. rewrite /lb. apply Rabs_case; apply Rmin_case_strong; destruct eps, eps' => /=; nra. }
Qed.

Lemma Rbar_at_right_witness_above (r: R) y P:
  Rbar_at_right r P -> r < y -> ∃ x, r < x < y ∧ P x.
Proof.
  intros. assert (Hpos: 0 < y - r) by nra.
  edestruct (Rbar_at_right_witness r (mkposreal _ Hpos) P) as (x&?&HP); auto.
  exists x. split; auto.
  simpl in H1. nra.
Qed.

Lemma Rbar_at_right_witness_above_m_infty y P:
  Rbar_at_right m_infty P -> ∃ x, x < y ∧ P x.
Proof.
  unfold Rbar_at_right, within, Rbar_locally.
  intros HM. destruct HM as (M&HM). exists (Rmin (M - 1) (y - 1)).
  split.
  - apply (Rle_lt_trans _ (y - 1)); last nra.
    apply Rmin_r.
  - apply HM; simpl; auto.
  - apply (Rle_lt_trans _ (M - 1)); last nra.
    apply Rmin_l.
Qed.

Lemma Rbar_at_right_strict_monotone (t : R) (a : Rbar) g glim :
  Rbar_lt a t →
  (∀ x y, x < y /\ Rbar_lt y t → Rbar_lt a x → g x < g y) →
  is_right_lim g a glim ->
  Rbar_at_right a (λ y : Rbar, Rbar_lt glim (g y)).
Proof.
  unfold is_left_lim.
  intros Hltb Ht (Hnm&Hlim).
  apply Classical_Prop.NNPP. intros Hneg%not_Rbar_at_right.
  destruct a; try congruence.
  - unfold filterlim, filter_le, filtermap in Hlim.
    assert (Hpos: 0 < t - r).
    { simpl in Hltb. nra. }
    set (eps' := mkposreal _ Hpos).
    specialize (Hneg eps').
    assert (∃ x : R, (r < x ∧ x < r + eps') ∧ Rbar_lt (g x) glim) as (x&Hrange&r0).
    {
      destruct Hneg as (x&Hrange&Hnlt).
      apply Rbar_not_lt_le in Hnlt.
      apply Rbar_le_lt_or_eq_dec in Hnlt.
      destruct Hnlt as [Hlt|Heq].
      { exists x. split; eauto. }
      destruct (interval_inhabited r x) as (x'&Hx'1&Hx'2); first nra.
      exists x'.
      split; first nra.
      rewrite -Heq. simpl. apply Ht; auto; simpl; try nra. split; try nra.
      move: Hrange. rewrite /eps' /=. nra.
    }
    apply open_Rbar_gt' in r0. apply Hlim in r0.
    eapply (Rbar_at_right_witness_above r x) in r0; try (intuition eauto; done).
    destruct r0 as (y&Hrange'&Hlt).
    simpl in Hlt. apply Rlt_not_le in Hlt.
    apply Hlt. left. apply Ht; simpl; simpl in Hltb; try nra.
    split; first by intuition.
    move: Hrange. rewrite /eps' /=. nra.
  - unfold filterlim, filter_le, filtermap in Hlim.
    specialize (Hneg t).
    assert (∃ x : R, x < t ∧ Rbar_lt (g x) glim) as (x&Hrange&r0).
    {
      destruct Hneg as (x&Hrange&Hnlt).
      apply Rbar_not_lt_le in Hnlt.
      apply Rbar_le_lt_or_eq_dec in Hnlt.
      destruct Hnlt as [Hlt|Heq].
      { exists x. split; eauto. }
      exists (x - 1).
      split; first nra.
      rewrite -Heq. simpl. apply Ht; auto; split; simpl; try nra.
    }
    apply open_Rbar_gt' in r0. apply Hlim in r0.
    eapply (Rbar_at_right_witness_above_m_infty x) in r0; try (intuition eauto; done).
    destruct r0 as (y&Hrange'&Hlt).
    simpl in Hlt. apply Rlt_not_le in Hlt.
    apply Hlt. left. apply Ht; simpl; simpl in Hltb; try nra.
Qed.

Lemma Rbar_at_right_strict_monotone' (t : Rbar) (a : Rbar) g glim :
  Rbar_lt a t →
  (∀ x y, x < y /\ Rbar_lt y t → Rbar_lt a x → g x < g y) →
  is_right_lim g a glim ->
  Rbar_at_right a (λ y : Rbar, Rbar_lt glim (g y)).
Proof.
  intros Hlt Hmono Hlim.
  destruct t.
  - eapply Rbar_at_right_strict_monotone; eauto.
  - destruct a as [r' | |].
    { eapply (Rbar_at_right_strict_monotone (Rmax 0 (r' + 1))); eauto.
      { simpl. apply Rmax_case_strong; nra. }
      { intros. apply Hmono; auto. split; intuition auto. }
    }
    { inversion Hlt. }
    { eapply (Rbar_at_right_strict_monotone 0); eauto.
      { intros. apply Hmono; auto. split; intuition auto. }
    }
  - destruct a; inversion Hlt.
Qed.

Section comp.

  Lemma R_dist_plus_r1 x y z y':
    R_dist x (y + z) <= R_dist x (y' + z) + R_dist y y'.
  Proof.
    rewrite /R_dist.
    replace (y + z) with (y' + z + (y - y')) by nra.
    replace (x - (y' + z + (y - y'))) with ((x - (y' + z)) - (y - y')) by nra.
    rewrite -(Rabs_Ropp (y - y')).
    etransitivity; last eapply Rabs_triang.
    reflexivity.
  Qed.

  Lemma linear_interp_bound startv endv a b x :
    a < b ->
    a <= x <= b -> 
    Rmin startv endv <= startv + (endv - startv) * ((x -a)/(b-a)) <= Rmax startv endv.
  Proof.
    intros Hlt Hrange.
    destruct (Rle_dec startv endv).
    {
      rewrite Rmin_left //. rewrite Rmax_right; last by nra.
      split.
      { transitivity (startv + 0); first nra.
        apply Rplus_le_compat_l.
        apply Rmult_le_pos; first nra.
        apply Rdiv_le_0_compat; nra.
      }
      { transitivity (startv + (endv - startv) * 1); last nra.
        apply Rplus_le_compat_l.
        apply Rmult_le_compat_l; first nra.
        apply Rle_div_l; nra.
      }
    }
    {
      rewrite Rmin_right; last nra. rewrite Rmax_left; last by nra.
      split.
      { transitivity (startv + (endv - startv) * 1); first nra.
        apply Rplus_le_compat_l.
        apply Rmult_le_compat_neg_l; first nra.
        apply Rle_div_l; nra.
      }
      { transitivity (startv + 0); last nra.
        apply Rplus_le_compat_l.
        apply Rmult_le_0_r; first nra.
        apply Rdiv_le_0_compat; nra.
      }
    }
  Qed.

  Lemma linear_interp_bound_abs startv endv a b x :
    a < b ->
    a <= x <= b -> 
    Rabs (startv + (endv - startv) * ((x -a)/(b-a))) <= Rmax (Rabs startv) (Rabs endv).
  Proof.
    intros Hlt Hrange.
    specialize (linear_interp_bound startv endv a b x Hlt Hrange).
    remember ((startv + (endv - startv) * ((x -a)/(b-a)))) as y.
    clear Heqy.
    apply Rmin_case_strong; repeat apply Rmax_case_strong; repeat (apply Rabs_case); try nra.
  Qed.

  Lemma continuity_linear_interp startv endv a b :
    a < b ->
    continuity (λ x0 : R, startv + (endv - startv) * ((x0 - a) * / (b - a))).
  Proof.
    intros Hlt.
    apply continuity_plus.
    { apply continuity_const => ? //=. }
    apply continuity_mult.
    { apply continuity_const => ? //=. }
    apply continuity_mult.
    { rewrite /Rminus.
      apply continuity_plus.
      { intros x. rewrite -continuous_continuity_pt. apply continuous_id. }
      apply continuity_opp.
      { apply continuity_const => ? //=. }
    }
    { apply continuity_const => ? //=. }
  Qed.

  Lemma constant_open_segment_ub_function_aux1 f a b v startv endv δ :
    constant_D_eq f (open_interval a b) v ->
    (f a <= startv) ->
    (v <= startv) ->
    (v <= endv) ->
    (f b <= endv) ->
    (0 < δ) ->
    (a + δ < b - δ) ->
    ∃ g, (∀ x, a <= x <= b -> f x <= g x) /\
         (∀ x, continuous g x) /\
         (∀ x, a <= x <= b -> Rabs (g x) <= Rmax (Rmax (Rabs (f a)) (Rabs (f b)))
                                                 (Rmax (Rabs v) (Rmax (Rabs startv) (Rabs endv)))) /\
         (∀ x, a + δ < x <= b - δ -> f x = g x) /\
         g a = startv /\
         g b = endv.
  Proof.
    intros Hconst Hle0 Hle0' Hle1 Hle2 Hdelt_nn Hdelt_range.
    exists (λ x, match Rle_dec x (a + δ) with
                 | left _ => startv + (v - startv) * ((x - a) * / ((a + δ) - a))
                 | _ =>
                   match Rle_dec x (b - δ) with
                   | left _ => v
                   | _ =>
                     v + (endv - v) * ((x - (b - δ)) * / (b - (b - δ)))
                   end
                 end).
    split.
    { intros x Hrange. destruct Rle_dec as [Hle|Hnle].
      {
        assert (x = a \/ a < x) as Hcases.
        { nra. }
        destruct Hcases as [-> | Hstrict ].
        { field_simplify; last nra.
          transitivity (startv); last by (right; field; nra).
          auto.
        }
        assert (f x = v) as ->.
        { apply Hconst. split; nra. }
        transitivity (startv + (v - startv) * 1).
        { right. field. }
        apply Rplus_le_compat_l. apply Rmult_le_compat_neg_l.
        { nra. }
        rewrite -Rdiv_le_1; first nra.
        nra.
      }
      destruct Rle_dec.
      { right. apply Hconst. split; nra. }
      assert (x = b \/ x < b) as [->|Hlt].
      { nra. }
      { field_simplify; nra. }
      assert (f x = v) as ->.
      { apply Hconst. split; nra. }
      transitivity (v + 0).
      { nra. }
      apply Rplus_le_compat_l.
      apply Rmult_le_pos; first nra.
      apply Rdiv_le_0_compat; nra.
    }
    split.
    {
      intros x.
      apply continuous_continuity_pt.
      eapply piecewise_continuity'.
      {
        eapply continuity_linear_interp. nra.
      }
      { eapply piecewise_continuity'.
        { apply continuity_const => ? //=. }
        { apply continuity_linear_interp. nra. }
        nra.
      }
      destruct (Rle_dec _ _); try nra.
      field. nra.
    }
    split.
    {
      intros x Hrange. destruct Rle_dec as [Hle|Hnle].
      { etransitivity; first eapply linear_interp_bound_abs; try nra.
        { repeat (apply Rmax_case_strong); nra. }
      }
      destruct Rle_dec as [Hle'|Hnle'].
      { repeat (apply Rmax_case_strong); nra. }
      { etransitivity; first eapply linear_interp_bound_abs; try nra.
        repeat (apply Rmax_case_strong); nra. }
    }
    split.
    {
      intros x Hrange.
      destruct Rle_dec; first nra.
      destruct Rle_dec; last nra.
      apply Hconst. rewrite /open_interval. split; nra.
    }
    split.
    {
      destruct Rle_dec; nra.
    }
    {
      destruct Rle_dec; first nra.
      destruct Rle_dec; first nra.
      field. nra.
    }
  Qed.

  Lemma constant_open_segment_ub_function f a b v (eps : posreal) startv endv :
    a <= b ->
    constant_D_eq f (open_interval a b) v ->
    (f a <= startv) ->
    (v <= startv) ->
    (v <= endv) ->
    (f b <= endv) ->
    (a = b -> startv = endv) ->
    ∃ g, (∀ x, a <= x <= b -> f x <= g x) /\
         (∀ x, continuous g x) /\
         ex_RInt (λ x, g x - f x) a b /\
         (RInt (λ x, g x - f x) a b < eps) /\
         g a = startv /\
         g b = endv.
  Proof.
    intros Hle0 Hconst Hlestartv1 Hlestartv2 Hle1 Hle2 Hcase.
    assert (Hintegrablef: ∀ x y, a <= x /\ x <= y /\ y <= b -> ex_RInt f x y).
    {
      intros x y Hle.
      apply: (ex_RInt_Chasles_2 _ a); first nra.
      apply: (ex_RInt_Chasles_1 _ _ _ b); first nra.
      eapply (ex_RInt_ext (λ x, v)).
      { rewrite Rmin_left // Rmax_right //. intros; symmetry; apply Hconst; split; nra. }
      eapply ex_RInt_const.
    }
    destruct Hle0 as [Hlt|Heq]; last first.
    { subst. exists (λ x, endv).
      split.
      { intros x ?. assert (x = b) by nra. subst. eauto. }
      split.
      { intros x ?. apply continuous_const. }
      split.
      { apply: ex_RInt_minus; last by (eapply Hintegrablef; nra). apply ex_RInt_const. }
      { rewrite RInt_point /zero/=. destruct eps => /=; nra. }
    }
    set (M := Rmax (Rmax (Rabs (f a)) (Rabs (f b)))
                   (Rmax (Rabs v) (Rmax (Rabs startv) (Rabs endv)))).
    assert (Hfabs: ∀ x, a <= x <= b -> Rabs (f x) <= M).
    { intros ? Hrange. rewrite /M.
      assert (f x = v \/ f x = f a \/ f x = f b) as [->|[-> | ->]].
      { destruct Hrange as ([?|?]&[?|?]); subst; try nra;
        try (left; apply Hconst; split; nra).
      }
      { repeat apply Rmax_case_strong; try nra. }
      { repeat apply Rmax_case_strong; try nra. }
      { repeat apply Rmax_case_strong; try nra. }
    }
    assert (M = 0 ∨ 0 < M) as [HM0|HMnz].
    { rewrite /M.
      repeat (apply Rmin_case_strong || apply Rmax_case_strong || apply Rabs_case); try nra.
    }
    { assert (f a = 0 /\ f b = 0 /\ v = 0 /\ startv = 0 /\ endv = 0) as (?&?&?&?&?).
      { move: HM0. rewrite /M.
      repeat (apply Rmin_case_strong || apply Rmax_case_strong || apply Rabs_case); try nra. }
      exists (λ x, 0).
      assert (Hf0: ∀ x, a <= x <= b → f x = 0).
      { intros y (Hle1'&Hle2'). destruct Hle1'; last first.
        { subst. nra. }
        destruct Hle2'; last first.
        { subst. nra. }
        transitivity v; last done. apply Hconst. rewrite /open_interval; nra.
      }
      split.
      { intros. rewrite Hf0 //. nra. }
      split.
      { apply continuous_const. }
      split.
      { apply: ex_RInt_minus; last by (eapply Hintegrablef; nra). apply ex_RInt_const. }
      split; last by (split; congruence).
      eapply (Rle_lt_trans _ 0); last by (destruct eps => /=; nra).
      right.
      erewrite (RInt_ext _ (λ _, 0)).
      { rewrite RInt_const /scal/=/mult/=. nra. }
      intros x. apply Rmin_case_strong; apply Rmax_case_strong; intros; rewrite Hf0 //; nra.
    }
    set (δ := Rmin ((b - a)/3) ((eps / (8 * M)))).
    assert (0 < δ).
    { rewrite /δ.
      apply Rmin_case_strong; first by nra.
      intros _. apply Rdiv_lt_0_compat; destruct eps => /=; nra.
    }
    assert ((a + δ < b - δ)).
    { rewrite /δ. apply Rmin_case_strong; nra. }
    edestruct (constant_open_segment_ub_function_aux1 f a b v startv endv δ) as (g&Hg1&Hg2&Hg3&Hg4&Hg5); eauto.
    exists g.
    assert (Hintegrableh: ∀ x y, a <= x /\ x <= y /\ y <= b -> ex_RInt (λ x, g x - f x) x y).
    {
      intros.
      apply: (ex_RInt_Chasles_2 _ a); first nra.
      apply: (ex_RInt_Chasles_1 _ _ _ b); first nra.
      apply: ex_RInt_minus; last eapply Hintegrablef; try nra.
      eapply ex_RInt_continuous; auto.
    }
    repeat (split; auto).
    eapply Hintegrableh; eauto; nra.
    eapply (Rle_lt_trans _ (RInt (λ x, g x - f x) a (a + δ) +
                            RInt (λ x, g x - f x) (a+δ) (b - δ) +
                            RInt (λ x, g x - f x) (b - δ) b)).
    {
      rewrite -(RInt_Chasles (λ x, g x - f x) a (a + δ)); try (eapply Hintegrableh; nra).
      rewrite -(RInt_Chasles (λ x, g x - f x) (a + δ) (b - δ)); try (eapply Hintegrableh; nra).
      rewrite /plus/=. right. field.
    }
    eapply (Rlt_le_trans _ (eps/2 + 0 + eps/2)); last first.
    { right. field. }
    apply Rplus_lt_compat.
    assert (RInt (λ x, g x - f x) (a + δ) (b - δ) = 0) as ->.
    { rewrite (RInt_ext _ (λ x, 0)); last first.
      { rewrite Rmin_left // ?Rmax_right //; try nra. intros. rewrite Hg4; try nra.  }
      rewrite RInt_const. rewrite /scal/=/mult/=. nra. }
    apply Rplus_lt_compat_r.
    { eapply Rle_lt_trans; first eapply (RInt_le _ (λ x, 2 * M)); try nra.
      { apply Hintegrableh. nra. }
      { apply ex_RInt_const. }
      { intros.
        transitivity (Rabs (g x) + Rabs (f x)).
        { repeat apply Rabs_case; nra. }
        { setoid_rewrite Hfabs; last nra. setoid_rewrite Hg3; last nra. right. rewrite /M. field. }
      }
      rewrite RInt_const. replace (a + δ -a) with δ by nra. rewrite /scal/=/mult/=.
      eapply (Rle_lt_trans _ ((eps / (8 * M)) * (2 * M))).
      { apply Rmult_le_compat_r; first nra.
        apply Rmin_r. }
      field_simplify; last nra. assert (2 * eps / 8 = eps / 4) as -> by field.
      rewrite /Rdiv. apply Rmult_lt_compat_l; first by (destruct eps => /=; nra).
      nra.
    }
    { eapply Rle_lt_trans; first eapply (RInt_le _ (λ x, 2 * M)); try nra.
      { apply Hintegrableh. nra. }
      { apply ex_RInt_const. }
      { intros.
        transitivity (Rabs (g x) + Rabs (f x)).
        { repeat apply Rabs_case; nra. }
        { setoid_rewrite Hfabs; last nra. setoid_rewrite Hg3; last nra. right. rewrite /M. field. }
      }
      rewrite RInt_const. replace (b - (b - δ)) with δ by nra. rewrite /scal/=/mult/=.
      eapply (Rle_lt_trans _ ((eps / (8 * M)) * (2 * M))).
      { apply Rmult_le_compat_r; first nra.
        apply Rmin_r. }
      field_simplify; last nra. assert (2 * eps / 8 = eps / 4) as -> by field.
      rewrite /Rdiv. apply Rmult_lt_compat_l; first by (destruct eps => /=; nra).
      nra.
    }
  Qed.


Lemma Riemann_integrable_SF_aux a b sf (eps: posreal) :
  (∀ t : R, Rmin a b <= t <= Rmax a b → Rabs (sf t - sf t) <= {| fe := fct_cte 0; pre := StepFun_P4 a b 0 |} t)
  ∧ Rabs (RiemannInt_SF {| fe := fct_cte 0; pre := StepFun_P4 a b 0 |}) < eps.
Proof.
  split.
  - intros; replace (sf t - sf t) with 0 by nra; rewrite Rabs_right => //=; last nra; rewrite /fct_cte; nra.
  - simpl. rewrite StepFun_P18 Rabs_right => //=; destruct eps => /=; nra.
Qed.

Lemma Riemann_integrable_SF a b (sf: StepFun a b) :
  Riemann_integrable sf a b.
Proof.
  rewrite /Riemann_integrable => eps.
  exists sf.
  exists (mkStepFun (StepFun_P4 a b 0)).
  apply Riemann_integrable_SF_aux.
Defined.


  Lemma StepFun_ub (f: R -> R) (a b : R) :
    a <= b ->
    IsStepFun f a b ->
    ∃ M, (∀ x, a <= x <= b -> f x <= M).
  Proof.
    rewrite /IsStepFun. intros Hle (l&Hsub).
    revert a Hle Hsub.
    induction l as [| x1 l IHl].
    { intros. destruct Hsub as (l'&Hadapted).
      destruct Hadapted as (?&Hmin&?&Hfalse&_).
      inversion Hfalse. }
    { intros a Hle Hsub.
      destruct Hsub as (l'&Hadapted).
      destruct l as [| x2 l].
      { destruct Hadapted as (?&Hmin&Hmax&Hlen&?).
        destruct l' as [|]; last first.
        { simpl in Hlen. congruence. }
        assert (a = b) as <-.
        { simpl in Hmin, Hmax. move: Hmin Hmax. apply Rmin_case_strong; apply Rmax_case_strong; nra. }
        exists (f a). intros x ?. assert (x = a) by nra. subst; reflexivity. }
      destruct l' as [|y l'].
      { destruct Hadapted as (?&Hmin&Hmax&Hlen&?).
        simpl in Hlen. congruence. }
      specialize (StepFun_P7 Hle Hadapted) => Hadapted_tl.
      assert (Hlex2: x2 <= b).
      { destruct Hadapted as (Hordered&Hmin&Hmax&Hlen&?).
        replace x2 with (RList.pos_Rl (x1 :: x2 :: l) 1) by auto.
        rewrite Rmax_right // in Hmax. rewrite -Hmax.
        apply RList.RList_P6; auto.
        simpl. lia.
      }
      edestruct (IHl x2) as (M'&HM').
      { auto. }
      { eexists. eauto. }
      destruct Hadapted as (HOrdered&Hmin&Hmax&Hlen&Hval).
      assert (a = x1).
      { rewrite Rmin_left // in Hmin. }
      exists (Rmax (f a) (Rmax y M')).
      assert (Hconst: constant_D_eq f (open_interval x1 x2) y).
      { apply (Hval O). simpl. lia. }
      intros z Hrange.
      destruct (Rle_dec x2 z).
      { etransitivity; first eapply HM'; first by nra. 
        do 2 setoid_rewrite <-Rmax_r. reflexivity.
      }
      destruct (Req_appart_dec a z).
      { subst. apply Rmax_l. }
      setoid_rewrite <-Rmax_r.
      rewrite Hconst; first apply Rmax_l.
      split; nra.
    }
  Qed.

  Lemma StepFun_ub_fun_cont_aux (f: R -> R) (a b : R) (startv : R) (eps : posreal) :
    a <= b ->
    (∀ x, a <= x <= b -> f x <= startv) ->
    IsStepFun f a b ->
    ∃ g : R -> R, (∀ x, continuous g x) /\ (∀ x, a <= x <= b -> f x <= g x) /\
                  ex_RInt (λ x, g x - f x) a b /\
                  RInt (λ x, g x - f x) a b < eps /\
                  g a = startv.
  Proof.
    rewrite /IsStepFun. intros Hle Hstartv (l&Hsub).
    revert a startv eps Hle Hstartv Hsub.
    induction l as [| x1 l IHl].
    { intros. destruct Hsub as (l'&Hadapted).
      destruct Hadapted as (?&Hmin&?&Hfalse&_).
      inversion Hfalse. }
    { intros a startv eps Hle Hstartv Hsub.
      destruct Hsub as (l'&Hadapted).
      destruct l as [| x2 l].
      { destruct Hadapted as (?&Hmin&Hmax&Hlen&?).
        destruct l' as [|]; last first.
        { simpl in Hlen. congruence. }
        assert (a = b) as <-.
        { simpl in Hmin, Hmax. move: Hmin Hmax. apply Rmin_case_strong; apply Rmax_case_strong; nra. }
        subst.
        exists (fct_cte (startv)).
        split.
        { intros; apply continuous_continuity_pt. apply derivable_continuous, derivable_const. }
        split.
        { intros x' ?. assert (x' = a) as -> by nra. rewrite /fct_cte//=. apply Hstartv; eauto. }
        split.
        { apply ex_RInt_point. }
        split.
        { rewrite RInt_point /zero/=. destruct eps; auto. }
        rewrite /fct_cte//=. (* reflexivity. *)
      }
      destruct l' as [|y l'].
      { destruct Hadapted as (?&Hmin&Hmax&Hlen&?).
        simpl in Hlen. congruence. }
      specialize (StepFun_P7 Hle Hadapted) => Hadapted_tl.
      assert (Hlex2: x2 <= b).
      { destruct Hadapted as (Hordered&Hmin&Hmax&Hlen&?).
        replace x2 with (RList.pos_Rl (x1 :: x2 :: l) 1) by auto.
        rewrite Rmax_right // in Hmax. rewrite -Hmax.
        apply RList.RList_P6; auto.
        simpl. lia.
      }
      assert (x1 = x2 \/ x1 ≠ x2) as [Heq|Hneq] by nra.
      {
        subst. eapply IHl; eauto. exists l'.
        destruct Hadapted as (HOrdered&Hmin&Hmax&Hlen&Hval).
        rewrite Rmin_left // in Hmin. simpl in Hmin.  subst. eauto.
      }
      destruct Hadapted as (HOrdered&Hmin&Hmax&Hlen&Hval).
      assert (a = x1).
      { rewrite Rmin_left // in Hmin. }
      assert (a <= x2).
      { rewrite Rmin_left // in Hmin.
        replace x2 with (RList.pos_Rl (x1 :: x2 :: l) 1) by auto.
        rewrite -Hmin.
        rewrite RList.RList_P6 in HOrdered * => HOrdered. eapply HOrdered; eauto.
        simpl. lia.
      }
      edestruct (IHl x2 startv (mkposreal _ (is_pos_div_2 eps))) as (g&Hgcont&Hgub&Hex&Hint&?).
      { auto. }
      { intros. apply Hstartv; nra. }
      { eexists. eauto. }
      assert (Hconst: constant_D_eq f (open_interval x1 x2) y).
      { apply (Hval O). simpl. lia. }
      assert (y <= startv).
      { rewrite -(Hconst ((x1 + x2)/2)); first by (eapply Hstartv; nra).
        split; nra. }
      edestruct (constant_open_segment_ub_function f a x2 y (mkposreal _ (is_pos_div_2 eps))
                                                   startv
                                                   startv) as (g'&Hg1'&Hg2'&Hgex'&Hg3'&Hg4'&?).
      { auto. }
      { subst. eauto. }
      { eapply Hstartv; nra. }
      { auto. }
      { auto. }
      { eapply Hstartv; nra. }
      { trivial. }
      exists (λ x, match Rle_dec x x2 with
                   | left _ => g' x
                   | _ => g x
                   end).
      split.
      {
        intros z. apply continuous_continuity_pt, piecewise_continuity'.
        { intros x. apply continuous_continuity_pt. auto. }
        { intros x. apply continuous_continuity_pt. auto. }
        intuition; congruence.
      }
      split.
      {
        intros z Hrange. destruct Rle_dec; auto.
        { apply Hg1'; nra. }
        { apply Hgub; nra. }
      }
      assert (ex_RInt (λ x : R, (match Rle_dec x x2 with | left _ => g' x | _ => g x end) - f x) a b).
      {
        eapply (ex_RInt_Chasles _ _ x2).
        { eapply ex_RInt_ext; try eassumption. rewrite Rmin_left // ?Rmax_right; try nra. intros.
          destruct Rle_dec => /=; first reflexivity.
          nra. }
        { eapply ex_RInt_ext; try eassumption. rewrite Rmin_left // ?Rmax_right; try nra. intros.
          destruct Rle_dec => /=; first nra.
          reflexivity. }
      }
      split; auto.
      split.
      {
        rewrite -(RInt_Chasles _ _ x2); last first.
        { apply: (ex_RInt_Chasles_2 _ a); first nra; auto.  }
        { apply: (ex_RInt_Chasles_1 _ _ _ b); first nra; auto. }
        replace (eps : R) with (eps/2 + eps/2) by field.
        apply Rplus_lt_compat.
        { setoid_rewrite RInt_ext; first eapply Hg3'.
          rewrite Rmin_left // Rmax_right //; intros. destruct Rle_dec; try nra. }
        { setoid_rewrite RInt_ext; first eapply Hint.
          rewrite Rmin_left // Rmax_right //; intros. destruct Rle_dec; try nra. }
      }
      destruct Rle_dec; try nra.
    }
  Qed.

  Lemma StepFun_ub_fun_cont (f: R -> R) (a b : R) (eps : posreal) :
    a <= b ->
    IsStepFun f a b ->
    ∃ g : R -> R, (∀ x, continuous g x) /\ (∀ x, a <= x <= b -> f x <= g x) /\
                  ex_RInt (λ x, g x - f x) a b /\
                  RInt (λ x, g x - f x) a b < eps.
  Proof.
    intros.
    edestruct (StepFun_ub f a b) as (M&HM); eauto.
    edestruct (StepFun_ub_fun_cont_aux f a b M eps) as (g&?); eauto.
    exists g. intuition.
  Qed.

  Lemma StepFun_P28' : ∀ (a b l : R) f g,
      IsStepFun f a b ->
      IsStepFun g a b->
      IsStepFun (λ x : R, f x + l * g x) a b.
  Proof.
    intros a b l f g Hstep1 Hstep2.
    destruct Hstep1 as (?&?).
    destruct Hstep2 as (?&?).
    eexists.
    eapply StepFun_P27; eauto.
  Qed.

  Lemma StepFun_lb_fun_cont (f: R -> R) (a b : R) (eps : posreal) :
    a <= b ->
    IsStepFun f a b ->
    ∃ g : R -> R, (∀ x, continuous g x) /\ (∀ x, a <= x <= b -> g x <= f x) /\
                  ex_RInt (λ x, f x - g x) a b /\
                  RInt (λ x, f x - g x) a b < eps.
  Proof.
    intros Hle Hstep.
    edestruct (StepFun_ub_fun_cont (λ x, fct_cte 0 x + -1 * (f x)) a b eps) as (gopp&Hgopp); auto.
    {
      eapply StepFun_P28'.
      { apply StepFun_P4. }
      { eauto. }
    }
    destruct Hgopp as (Hg1&Hg2&Hg3&Hg4).
    exists (λ x, Ropp (gopp x)).
    split.
    { intros. apply: continuous_opp; intuition eauto. }
    split.
    { intros x Hrange. specialize (Hg2 x Hrange). rewrite /fct_cte in Hg2. nra. }
    split.
    { eapply ex_RInt_ext; eauto. intros. rewrite /=/fct_cte. field. }
    { erewrite RInt_ext; eauto. intros. rewrite /=/fct_cte. field. }
  Qed.


Instance Rle_trans_proper_left: Proper (Rle ==> eq ==> flip impl) Rle.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rle_trans_proper_right: Proper (eq ==> Rle ==> impl) Rle.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rlt_trans_proper_left: Proper (Rlt ==> eq ==> flip impl) Rlt.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rlt_trans_proper_right: Proper (eq ==> Rlt ==> impl) Rlt.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rlt_Rle_trans_proper_left: Proper (Rle ==> eq ==> flip impl) Rlt.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.
Instance Rlt_Rle_trans_proper_right: Proper (eq ==> Rle ==> impl) Rlt.
Proof. intros ?? Hle ?? Hle'. rewrite /flip/impl/=. nra. Qed.

Lemma RiemannInt_SF_proof_irrel a b f (Hpf1 Hpf2 : IsStepFun _ a b) :
  RiemannInt_SF  {| fe := f; pre := Hpf1 |} =
  RiemannInt_SF  {| fe := f; pre := Hpf2 |}.
Proof.
  destruct (Rle_dec a b).
  { apply Rle_antisym; apply StepFun_P37; eauto; intros => //=; nra. }
  rewrite StepFun_P39.
  symmetry. rewrite StepFun_P39.
  f_equal.
  { apply Rle_antisym; apply StepFun_P37; eauto; intros => //=; nra. }
Qed.

Lemma StepFun_P30':
  ∀ (a b l : R) (f g : StepFun a b) (Hpf : IsStepFun _ a b),
    RiemannInt_SF {| fe := λ x : R, f x + l * g x; pre := Hpf |} =
    RiemannInt_SF f + l * RiemannInt_SF g.
Proof.
  intros. rewrite -StepFun_P30.
  apply RiemannInt_SF_proof_irrel.
Qed.

Lemma RiemannInt_SF_ext :
  ∀ (a b : R) (f g : StepFun a b), (∀ x : R, Rmin a b <= x <= Rmax a b -> f x = g x) →
                                   RiemannInt_SF f = RiemannInt_SF g.
Proof.
  intros a b f g Heq.
  destruct (Rle_dec a b).
  { apply Rle_antisym; apply StepFun_P37; eauto; intros => //=; rewrite ?Heq; try nra;
    rewrite ?Rmin_left // ?Rmax_right //; nra. }
  rewrite StepFun_P39.
  symmetry. rewrite StepFun_P39.
  f_equal.
  { apply Rle_antisym; apply StepFun_P37; eauto; intros => //=; rewrite ?Heq; try nra;
    rewrite ?Rmax_left // ?Rmin_right //; nra. }
Qed.

Lemma RiemannInt_SF_ext' :
  ∀ (a b : R) (a' b': R) (f : StepFun a b) (g : StepFun a' b'),
    a = a' -> b = b' -> (∀ x : R, Rmin a b <= x <= Rmax a b -> f x = g x) → RiemannInt_SF f = RiemannInt_SF g.
Proof.
  intros a b a' b' f g ?? Heq.
  subst. eapply RiemannInt_SF_ext; eauto.
Qed.
Lemma seq2Rlist_id l : seq2Rlist l = l.
Proof. induction l => //=; congruence. Qed.

Lemma size_compat: ∀ s : list R, Datatypes.length s = seq.size s.
Proof. intros. rewrite -size_compat. rewrite seq2Rlist_id //. Qed.

Lemma R_dist_lt_all_eps' v1 v2 :
  (∀ (eps: posreal), R_dist v1 v2 < eps) -> ~ v1 < v2.
Proof.
  intros Hlt_eps Hlt.
  assert (Hpos: 0 < v2 - v1) by nra.
  specialize (Hlt_eps (mkposreal _ Hpos)).
  rewrite R_dist_sym in Hlt_eps.
  rewrite /R_dist Rabs_right //= in Hlt_eps; nra.
Qed.

Lemma R_dist_lt_all_eps v1 v2 :
  (∀ (eps: posreal), R_dist v1 v2 < eps) -> v1 = v2.
Proof.
  intros Hlt.
  destruct (Rle_dec v1 v2) as [[|]|n]; auto.
  { exfalso; eapply R_dist_lt_all_eps'; eauto. }
  apply Rnot_le_lt in n.
  { exfalso; eapply R_dist_lt_all_eps'; last eauto. intros. rewrite R_dist_sym; eauto. }
Qed.

Lemma RiemannInt_SF_RiemannInt a b (sf: StepFun a b) :
  RiemannInt (Riemann_integrable_SF a b sf) = RiemannInt_SF sf.
Proof.
  rewrite /RiemannInt//=.
  destruct (RiemannInt_exists _ _ _) as (v&Hv).
  rewrite /Un_cv//= in Hv.
  rewrite /phi_sequence/Riemann_integrable_SF/= in Hv.
  symmetry.
  apply R_dist_lt_all_eps. intros. edestruct (Hv eps) as (n&Hlt).
  { destruct eps; eauto. }
  apply (Hlt n); lia.
Qed.

Lemma is_RInt_of_SF a b (sf: StepFun a b) :
  a <= b ->
  is_RInt sf a b (RiemannInt_SF sf).
Proof. rewrite -RiemannInt_SF_RiemannInt. intros. apply: ex_RInt_Reals_aux_1. Qed.

Lemma ex_RInt_of_SF a b (sf: StepFun a b) :
  a <= b ->
  ex_RInt sf a b.
Proof. intros; eexists; eapply is_RInt_of_SF; auto. Qed.

Lemma RInt_of_SF a b (sf: StepFun a b) :
  a <= b ->
  RInt sf a b = RiemannInt_SF sf.
Proof. intros. by apply is_RInt_unique, is_RInt_of_SF. Qed.

Lemma is_pos_div_4: ∀ eps : posreal, 0 < eps / 4.
Proof.
  intros. specialize (is_pos_div_2 (mkposreal (eps /2) (is_pos_div_2 _))) => //=.
  nra.
Qed.

Lemma posreal_div_2_lt (eps: posreal) :
  eps / 2 < eps.
Proof.
  cut (eps < eps + eps).
  { nra. }
  destruct eps => //=. nra.
Qed.

  Lemma ex_RInt_ub_StepFun (f: R -> R) (a b : R) (eps : posreal) :
    a <= b ->
    ex_RInt f a b ->
    ∃ g : StepFun a b, (∀ x, a <= x <= b -> f x <= g x) /\
                       ex_RInt (λ x, g x - f x) a b /\
                       RInt (λ x, g x - f x) a b < eps.
  Proof.
    intros Hle Hex.
    assert (Hex': Riemann_integrable f a b) by auto using ex_RInt_Reals_0.
    destruct (Hex' (mkposreal _ (is_pos_div_2 eps))) as (phi&psi&Hphi&Hpsi).
    assert (X: IsStepFun (λ x, phi x + 1 * psi x) a b).
    { apply StepFun_P28; auto. }
    exists (mkStepFun X).
    split.
    { simpl. intros x Hrange. exploit (Hphi x). rewrite Rmin_left // Rmax_right //.
      apply Rabs_case; nra. }
    assert (ex_RInt (λ y : R, phi y + 1 * psi y) a b).
    {
      { apply: ex_RInt_plus.
        { apply ex_RInt_Reals_1. apply Riemann_integrable_SF. }
        { apply: ex_RInt_scal. apply ex_RInt_Reals_1. apply Riemann_integrable_SF. }
      }
    }
    assert (ex_RInt (λ x : R, phi x + 1 * psi x - f x) a b).
    { simpl. apply: ex_RInt_minus; auto. }
    split; simpl; auto.
    assert (ex_RInt psi a b).
    { apply ex_RInt_Reals_1. apply Riemann_integrable_SF. }
    eapply (Rle_lt_trans _ (RInt (λ t, 2 * psi t) a b)); last first.
    { rewrite RInt_scal //. rewrite /scal/=/mult/=.
      rewrite RInt_of_SF //. simpl in Hpsi. move: Hpsi. apply Rabs_case; nra.
    }
    simpl. eapply RInt_le; eauto.
    { apply: ex_RInt_scal; auto. }
    rewrite Rmin_left // Rmax_right // in Hphi.
    intros x Hrange.
    exploit (Hphi x); first nra. apply Rabs_case; nra.
  Qed.

  Lemma ex_RInt_lb_StepFun (f: R -> R) (a b : R) (eps : posreal) :
    a <= b ->
    ex_RInt f a b ->
    ∃ g : StepFun a b, (∀ x, a <= x <= b -> g x <= f x) /\
                       ex_RInt (λ x, f x - g x) a b /\
                       RInt (λ x, f x - g x) a b < eps.
  Proof.
    intros Hle Hex.
    assert (Hex': Riemann_integrable f a b) by auto using ex_RInt_Reals_0.
    destruct (Hex' (mkposreal _ (is_pos_div_2 eps))) as (phi&psi&Hphi&Hpsi).
    assert (X: IsStepFun (λ x, phi x + - 1 * psi x) a b).
    { apply StepFun_P28; auto. }
    exists (mkStepFun X).
    split.
    { simpl. intros x Hrange. exploit (Hphi x). rewrite Rmin_left // Rmax_right //.
      apply Rabs_case; nra. }
    assert (ex_RInt (λ y : R, phi y + - 1 * psi y) a b).
    {
      { apply: ex_RInt_plus.
        { apply ex_RInt_Reals_1. apply Riemann_integrable_SF. }
        { apply: ex_RInt_scal. apply ex_RInt_Reals_1. apply Riemann_integrable_SF. }
      }
    }
    assert (ex_RInt (λ x : R, f x - (phi x + - 1 * psi x)) a b).
    { simpl. apply: ex_RInt_minus; auto. }
    split; simpl; auto.
    assert (ex_RInt psi a b).
    { apply ex_RInt_Reals_1. apply Riemann_integrable_SF. }
    eapply (Rle_lt_trans _ (RInt (λ t, 2 * psi t) a b)); last first.
    { rewrite RInt_scal //. rewrite /scal/=/mult/=.
      rewrite RInt_of_SF //. simpl in Hpsi. move: Hpsi. apply Rabs_case; nra.
    }
    simpl. eapply RInt_le; eauto.
    { apply: ex_RInt_scal; auto. }
    rewrite Rmin_left // Rmax_right // in Hphi.
    intros x Hrange.
    exploit (Hphi x); first nra. apply Rabs_case; nra.
  Qed.

  Lemma ex_RInt_bounding (f: R -> R) (a b : R) (eps : posreal) :
    a <= b ->
    ex_RInt f a b ->
    ∃ g1 g2, (∀ x, a <= x <= b -> g1 x <= f x <= g2 x) /\
             (∀ x, a <= x <= b -> continuous g1 x) /\
             (∀ x, a <= x <= b -> continuous g2 x) /\
             (RInt (λ x, g2 x - g1 x) a b < eps).
  Proof.
    intros Hle Hex.
    set (eps' := mkposreal _ (is_pos_div_4 eps)).
    edestruct (ex_RInt_ub_StepFun f a b eps') as ((g2'&Hisg2')&Hg2'); eauto.
    edestruct (ex_RInt_lb_StepFun f a b eps') as ((g1'&Hisg1')&Hg1'); eauto.
    edestruct (StepFun_ub_fun_cont g2' a b eps') as (g2&Hg2); eauto.
    edestruct (StepFun_lb_fun_cont g1' a b eps') as (g1&Hg1); eauto.
    exists g1, g2.
    destruct Hg1' as (Hg1lb'&Hg1ex'&Hg1RInt').
    destruct Hg2' as (Hg2lb'&Hg2ex'&Hg2RInt').
    destruct Hg1 as (Hg1cont&Hg1lb&Hg1ex&Hg1RInt).
    destruct Hg2 as (Hg2cont&Hg2lb&Hg2ex&Hg2RInt).
    split.
    { intros x Hrange.
      specialize (Hg1lb _ Hrange).
      specialize (Hg2lb _ Hrange).
      specialize (Hg1lb' _ Hrange).
      specialize (Hg2lb' _ Hrange).
      simpl in Hg2lb'. simpl in Hg1lb'.
      nra.
    }
    split; eauto.
    split; eauto.
    simpl in Hg2RInt'.
    simpl in Hg1RInt'.
    simpl in Hg1ex'.
    simpl in Hg2ex'.
    eapply (Rle_lt_trans _ (RInt (λ x, (g2 x - g2' x) + (g2' x - f x) + (f x - g1' x) + (g1' x - g1 x)) a b)).
    { right. eapply RInt_ext. intros. ring_simplify. reflexivity. }
    rewrite RInt_plus; eauto; last first.
    { repeat (apply: ex_RInt_plus; eauto). }
    rewrite RInt_plus; eauto; last first.
    { repeat (apply: ex_RInt_plus; eauto). }
    rewrite RInt_plus; eauto; last first.
    rewrite /plus/=.
    eapply (Rlt_le_trans _ (eps/4 + eps/4 + eps/4 + eps/4)).
    {
      repeat (apply Rplus_lt_compat; auto).
    }
    nra.
  Qed.

  Lemma is_RInt_bounding (f: R -> R) (a b : R) v (eps : posreal) :
    a <= b ->
    is_RInt f a b v ->
    ∃ g1 g2 v1 v2, (∀ x, a <= x <= b -> g1 x <= f x <= g2 x) /\
             (∀ x, a <= x <= b -> continuous g1 x) /\
             (∀ x, a <= x <= b -> continuous g2 x) /\
             is_RInt g1 a b v1 /\
             is_RInt g2 a b v2 /\
             (RInt (λ x, g2 x - g1 x) a b < eps) /\
             v1 <= v <= v2.
  Proof.
    intros.
    destruct (ex_RInt_bounding f a b eps) as (g1&g2&Hrange&Hcont1&Hcont2&Hdiff); auto.
    { eexists; eauto. }
    exists g1, g2, (RInt g1 a b), (RInt g2 a b).
    split; eauto.
    split; eauto.
    split; eauto.
    assert (ex_RInt g1 a b).
    { apply: ex_RInt_continuous; eauto.
      rewrite Rmin_left // Rmax_right //. }
    assert (ex_RInt g2 a b).
    { apply: ex_RInt_continuous; eauto.
      rewrite Rmin_left // Rmax_right //. }
    split. { apply: RInt_correct; auto. }
    split. { apply: RInt_correct; auto. }
    split; auto.
    split.
    { erewrite <-(is_RInt_unique); eauto. apply RInt_le; eauto.
      { eexists; eauto. }
      { intros. eapply Hrange; nra. }
    }
    { erewrite <-(is_RInt_unique f a b v); eauto. apply RInt_le; eauto.
      { eexists; eauto. }
      { intros. eapply Hrange; nra. }
    }
  Qed.

  Lemma bounding_ex_RInt (f : R -> R) (a b : R) :
    a <= b ->
    (∀ eps : posreal, ∃ g1 g2, (∀ x, a <= x <= b -> g1 x <= f x <= g2 x) /\
             ex_RInt g1 a b /\
             ex_RInt g2 a b /\
             (RInt (λ x, g2 x - g1 x) a b < eps)) ->
    ex_RInt f a b.
  Proof.
    intros Hle Heps.
    apply ex_RInt_Reals_1.
    unfold Riemann_integrable. intros eps.
    set (eps' := mkposreal (eps/4) (is_pos_div_4 _)).
    set (eps'' := mkposreal (eps'/2) (is_pos_div_2 _)).
    specialize (Heps eps'').
    apply ClassicalEpsilon.constructive_indefinite_description in Heps as (g1&Heps).
    apply ClassicalEpsilon.constructive_indefinite_description in Heps as (g2&Heps).
    destruct Heps as (Hsandwich&Hexg1&Hexg2&Hdiff).
    assert (Hexdiff: ex_RInt (λ x, g2 x - g1 x) a b).
    { apply: ex_RInt_minus; eauto. }
    apply ex_RInt_Reals_0 in Hexg1.
    apply ex_RInt_Reals_0 in Hexg2.
    apply ex_RInt_Reals_0 in Hexdiff.
    destruct (Hexg1 eps') as (phi1&psi1&Hex1).
    destruct (Hexg2 eps') as (phi2&psi2&Hex2).
    destruct (Hexdiff eps'') as (phid&psid&Hexd).
    set (phi := λ x, phi1 x + 1 * phid x).
    assert (Hisphi: IsStepFun phi a b).
    { apply StepFun_P28. }
    set (psi_a := λ x, (mkStepFun (StepFun_P32 phid) x) + 1 * psi1 x).
    assert (Hispsi_a: IsStepFun psi_a a b).
    { apply StepFun_P28. }
    set (psi := λ x, mkStepFun Hispsi_a x + 2 * psid x).
    assert (Hispsi: IsStepFun psi a b).
    { apply StepFun_P28. }
    exists (mkStepFun Hisphi).
    exists (mkStepFun Hispsi).
    split.
    {
      intros t Hrange.
      rewrite /psi/=/psi_a/=.
      setoid_rewrite (R_dist_tri _ _ (g2 t)).
      rewrite /phi/=.
      setoid_rewrite (R_dist_plus_r1 (g2 t) _ _ (g1 t)).
      rewrite Rmult_1_l. rewrite {2}/R_dist.
      replace (g2 t - (g1 t + phid t)) with (g2 t - g1 t - phid t) by nra.
      destruct Hexd as (Hexd1&Hexd2).
      setoid_rewrite (Hexd1); auto.
      destruct Hex1 as (Hex11&Hex12).
      rewrite (R_dist_sym (phi1 t)).
      rewrite {2}/R_dist.
      setoid_rewrite Hex11; auto.
      assert (R_dist (f t) (g2 t) <= R_dist (g2 t) (g1 t)) as ->.
      { rewrite R_dist_sym. rewrite /R_dist. rewrite Rmin_left // Rmax_right // in Hrange.
        specialize (Hsandwich _ Hrange).
        rewrite ?Rabs_right; nra. }
      assert (R_dist (g2 t) (g1 t) <= Rabs (phid t) + psid t) as ->.
      { specialize (Hexd1 _ Hrange).
        rewrite /R_dist.
        cut (Rabs (g2 t - g1 t) - Rabs (phid t) <= psid t); first by nra.
        setoid_rewrite Rabs_triang_inv. auto.
      }
      nra.
    }
    rewrite /psi.
    rewrite (StepFun_P30').
    rewrite /psi_a.
    rewrite (StepFun_P30').
    setoid_rewrite Rabs_triang.
    setoid_rewrite Rabs_triang.
    rewrite ?Rabs_mult.
    destruct (Hex1) as (_&Hr1).
    destruct (Hex2) as (_&Hr2).
    destruct (Hexd) as (_&Hrd).
    replace (Rabs 1) with 1 by (rewrite Rabs_right; nra).
    rewrite Rmult_1_l.
    replace (Rabs 2) with 2 by (rewrite Rabs_right; nra).
    rewrite /eps'.
    cut (Rabs (RiemannInt_SF {| fe := λ x : R, Rabs (phid x); pre := StepFun_P32 phid |}) < eps').
    { move: Hr1 Hr2 Hrd.
      specialize (posreal_div_2_lt eps').
      { rewrite /eps'//=. intros. nra. }
    }
    rewrite -RInt_of_SF //=.
    assert (Hbound: ∀ x, a <= x <= b -> Rabs (phid x) <= Rabs (g2 x - g1 x - phid x) + (Rabs (g2 x - g1 x))).
    {
      intros x Hrange. rewrite -(Rabs_Ropp (g2 x - g1 x - phid x)).
      setoid_rewrite <-Rabs_triang. right. f_equal. nra.
    }
    assert (ex_RInt (λ x : R, Rabs (phid x)) a b).
    { apply ex_RInt_norm, ex_RInt_of_SF; auto. }
    rewrite Rabs_right; last first.
    { apply Rle_ge.
      apply RInt_ge_0; eauto.
      intros. apply Rabs_pos. }
    assert (ex_RInt (λ x : R, Rabs (g2 x - g1 x)) a b).
    { apply ex_RInt_norm; repeat apply: ex_RInt_minus;
      auto using ex_RInt_Reals_1, ex_RInt_of_SF. }
    assert (ex_RInt (λ y : R, Rabs (g2 y - g1 y - phid y)) a b).
    { apply ex_RInt_norm; repeat apply: ex_RInt_minus;
      auto using ex_RInt_Reals_1, ex_RInt_of_SF. }


    eapply Rle_lt_trans.
    { eapply RInt_le; auto; last first.
      { intros. eapply Hbound; nra. }
      { apply: ex_RInt_plus; auto. }
    }
    rewrite RInt_plus; auto.
    simpl.
    replace (eps /4) with (eps/4/2 + eps/4/2) by nra.
    apply Rplus_lt_compat.
    * eapply Rle_lt_trans.
      { apply (RInt_le _ psid); eauto.
        { apply ex_RInt_of_SF; eauto. }
        intros. apply Hexd. rewrite Rmin_left // Rmax_right //. nra.
      }
      eapply Rle_lt_trans; first eapply Rle_abs.
      rewrite RInt_of_SF //.
    * erewrite RInt_ext; first eauto.
      intros x. rewrite Rmin_left // Rmax_right // => ?. rewrite Rabs_right //.
      specialize (Hsandwich x). nra.
  Qed.

Lemma Rmin_diff_eq x y:
  Rmin x y = (x + y) / 2 - Rabs(x - y) / 2.
Proof.
  apply Rmin_case_strong; apply Rabs_case; nra.
Qed.

Lemma Rmax_diff_eq x y:
  Rmax x y = (x + y) / 2 + Rabs(x - y) / 2.
Proof.
  apply Rmax_case_strong; apply Rabs_case; nra.
Qed.

  Lemma bounding_ex_RInt_lt (f : R -> R) (a b : R) :
    a <= b ->
    (∀ eps : posreal, ∃ g1 g2, (∀ x, a < x < b -> g1 x <= f x <= g2 x) /\
             (ex_RInt g1 a b) /\
             (ex_RInt g2 a b) /\
             (RInt (λ x, g2 x - g1 x) a b < eps)) ->
    ex_RInt f a b.
  Proof.
    intros Hle Heps.
    eapply bounding_ex_RInt; eauto.
    intros eps.
    edestruct (Heps eps) as (g1&g2&Hrange&Hcont1&Hcont2&Hint).
    set (g1' := λ x,
                match Req_appart_dec x a with
                | left _ => f x
                | right _ =>
                  match Req_appart_dec x b with
                  | left _ => f x
                  | right _ => g1 x
                  end
                end).
    set (g2' := λ x,
                match Req_appart_dec x a with
                | left _ => f x
                | right _ =>
                  match Req_appart_dec x b with
                  | left _ => f x
                  | right _ => g2 x
                  end
                end).
    exists g1', g2'.
    split; [| split; [| split]].
    - intros x (Hr1&Hr2).
      rewrite /g1'/g2'.
      destruct (Req_appart_dec); try nra.
      destruct (Req_appart_dec); try nra.
      eapply Hrange; nra.
    - eapply ex_RInt_ext; last eapply Hcont1.
      rewrite Rmin_left // Rmax_right //.
      intros.
      rewrite /g1'/g2'.
      destruct (Req_appart_dec); try nra.
      destruct (Req_appart_dec); try nra.
    - eapply ex_RInt_ext; last eapply Hcont2.
      rewrite Rmin_left // Rmax_right //.
      intros.
      rewrite /g1'/g2'.
      destruct (Req_appart_dec); try nra.
      destruct (Req_appart_dec); try nra.
    - eapply Rle_lt_trans; last eassumption. right. eapply RInt_ext.
      rewrite Rmin_left // Rmax_right //.
      intros.
      rewrite /g1'/g2'.
      destruct (Req_appart_dec); try nra.
      destruct (Req_appart_dec); try nra.
  Qed.

  Lemma bounding_is_RInt_lt (f : R -> R) (a b : R) v :
    a <= b ->
    (∀ eps : posreal, ∃ g1 g2, (∀ x, a < x < b -> g1 x <= f x <= g2 x) /\
             (ex_RInt g1 a b) /\
             (ex_RInt g2 a b) /\
             (RInt (λ x, g2 x - g1 x) a b < eps) /\
             RInt g1 a b <= v <= RInt g2 a b) ->
    is_RInt f a b v.
  Proof.
    intros Hle Heps.
    cut (ex_RInt f a b /\ RInt f a b = v).
    { intros (?&<-). apply: RInt_correct; auto. }
    assert (ex_RInt f a b).
    { eapply bounding_ex_RInt_lt; eauto.
      intros eps.
      edestruct (Heps eps) as (g1&g2&Hsandwich&Hex1&Hex2&Hdiff&?).
      exists g1, g2; intuition.
    }
    split; auto.
    apply R_dist_lt_all_eps.
    intros eps.
    edestruct (Heps eps) as (g1&g2&Hsandwich&Hex1&Hex2&Hdiff&?).
    rewrite RInt_minus/minus/plus/opp/= in Hdiff; auto.
    assert (RInt g1 a b <= RInt f a b).
    { apply RInt_le; auto. intros. eapply Hsandwich. nra. }
    assert (RInt f a b <= RInt g2 a b).
    { apply RInt_le; auto. intros. eapply Hsandwich. nra. }
    rewrite /R_dist. apply Rabs_case; nra.
  Qed.


Lemma nonneg_derivative_interval_0 (g : R → R) dg a b:
  (∀ x, is_derive g x (dg x)) ->
  (∀ x y, a <= x /\ x <= y /\ y <= b -> g x <= g y) ->
  ∀ x : R, a < x < b -> 0 <= dg x.
Proof.
  intros Hderiv Hincr.
  intros x Hrange.
  set (h := λ x, g (constrain_lb_ub a b x)).
  set (dh := λ x, deriv_constrain_lb_ub a b x * dg (constrain_lb_ub a b x)).
  assert (Hderiv': ∀ x, is_derive h x (dh x)).
  { intros y. rewrite /h/dh.
    apply: is_derive_comp; last auto using deriv_constrain_lb_ub_correct.
    apply Hderiv.
  }
  cut (∀ x, 0 <= dh x).
  { intros Hnn. rewrite /dh in Hnn.
    specialize (Hnn (unconstrain_lb_ub a b x)).
    { rewrite constrain_lb_ub_inv in Hnn; last nra.
      exploit (deriv_constrain_lb_ub_pos a b (unconstrain_lb_ub a b x)); intros; nra.
    }
  }
  intros y.
  rewrite -(is_derive_unique _ _ _ (Hderiv' y)).
  assert (pr: derivable h).
  { intros z. apply ex_derive_Reals_0. eexists; eauto; eapply Hg; eauto. }
  rewrite -(Derive_Reals _ _ (pr y)).
  apply nonneg_derivative_0.
  rewrite /h.
  rewrite /increasing => r s Hle.
  apply Hincr.
  { split.
    apply constrain_lb_ub_spec; nra.
    split; last by (apply constrain_lb_ub_spec; nra).
    apply constrain_lb_ub_increasing; auto. nra.
  }
Qed.

Lemma is_RInt_comp_noncont (f : R -> R) (g dg : R -> R) (a b : R) :
  (ex_RInt f (g a) (g b)) ->
  (forall x y, Rmin a b <= x /\ x <= y /\ y <= Rmax a b -> g x <= g y) ->
  (forall x, Rmin a b <= x <= Rmax a b -> is_derive g x (dg x) /\ continuous dg x) ->
  is_RInt (fun y => scal (dg y) (f (g y))) a b (RInt f (g a) (g b)).
Proof.
  (* We start off the same way is is_RInt_comp proof from Coquelicot *)
  wlog: a b / (a < b) => [Hw|Hab].
    case: (total_order_T a b) => [[Hab'|Hab']|Hab'] Hf Hmono Hg.
    - exact: Hw.
    - rewrite Hab'.
      by rewrite RInt_point; apply: is_RInt_point.
    - rewrite <- (opp_opp (RInt f _ _)).
      apply: is_RInt_swap.
      rewrite opp_RInt_swap //.
        apply Hw => // .
        { by apply ex_RInt_swap. }
        by rewrite Rmin_comm Rmax_comm.
        by rewrite Rmin_comm Rmax_comm.
      rewrite -> Rmin_left by now apply Rlt_le.
      rewrite -> Rmax_right by now apply Rlt_le.

  wlog: g dg / (forall x : R, is_derive g x (dg x) /\ continuous dg x) => [Hw Hf Hmono Hg | Hg Hf Hmono _].
    rewrite -?(extension_C1_ext g dg a b) ; try by [left | right].
    set g0 := extension_C1 g dg a b.
    set dg0 := extension_C0 dg a b.
    apply is_RInt_ext with (fun y : R => scal (dg0 y) (f (g0 y))).
    + rewrite /Rmin /Rmax /g0 ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hx.
      apply f_equal2.
        by apply extension_C0_ext ; by apply Rlt_le, Hx.
      by apply f_equal, extension_C1_ext ; by apply Rlt_le, Hx.
    + apply Hw.
      * intros x ; split.
        apply extension_C1_is_derive.
          by apply Rlt_le.
            by intros ; apply Hg ; by split.
      * apply @extension_C0_continuous.
          by apply Rlt_le.
        intros ; apply Hg ; by split.
      * intros ; rewrite /g0 ?extension_C1_ext; auto; simpl; try nra.
      * intros ; rewrite /g0 ?extension_C1_ext; auto; simpl; try nra.
    intros ; split.
      apply extension_C1_is_derive.
        by apply Rlt_le.
      intros ; apply Hg ; by split.
    apply @extension_C0_continuous.
      by apply Rlt_le.
    by intros ; apply Hg ; by split.

    have cg : forall x, continuous g x.
      move => t Ht; apply: ex_derive_continuous.
      by exists (dg t); apply Hg.


    assert (g a <= g b).
    { apply (Hmono a b); nra. }

    apply bounding_is_RInt_lt; first nra.
      intros eps.
      edestruct (is_RInt_bounding f (g a) (g b) (RInt f (g a) (g b)) eps) as (h1&h2&v1&v2&Hhspec); eauto.
      { apply: RInt_correct; auto. }

      destruct Hhspec as (Hsandwich&Hh1cont&Hh2cont&His1&His2&Hint_diff&Hint_sandwich).

      exists (λ x, scal (dg x) (h1 (g x))).
      exists (λ x, scal (dg x) (h2 (g x))).
      assert (Hnndg: ∀ x, a < x < b -> 0 <= dg x).
      intros.
      eapply nonneg_derivative_interval_0; eauto.
      eapply Hg.

      split.
      {
        intros x Hrange.
        exploit (Hsandwich (g x)).
        { split; eapply Hmono; eauto; try nra. }
        intros. specialize (Hnndg _ Hrange).
        rewrite /scal//=/mult//=; nra.
      }
      split.
      { apply: ex_RInt_continuous.
        rewrite ?Rmin_left ?Rmax_right; try nra.
        intros x Hrange.
        apply: continuous_scal.
        { eapply Hg. }
        { eapply continuous_comp; eauto. apply Hh1cont; eauto.
          split; eapply Hmono; eauto; try nra. }
      }
      split.
      { apply: ex_RInt_continuous.
        rewrite ?Rmin_left ?Rmax_right; try nra.
        intros x Hrange.
        apply: continuous_scal.
        { eapply Hg. }
        { eapply continuous_comp; eauto. apply Hh2cont; eauto.
          split; eapply Hmono; eauto; try nra. }
      }
      split.
      {
        rewrite /scal/=/mult/=.
        rewrite RInt_minus.
        { rewrite ?RInt_comp'; try intros x; try nra.
          { rewrite -RInt_minus; auto; apply ex_RInt_continuous; rewrite ?Rmin_left ?Rmax_right //. }
          *  intros; apply Hh1cont. split; eapply Hmono; eauto; try nra.
          *  intros; apply Hg.
          *  intros; apply Hh2cont. split; eapply Hmono; eauto; try nra.
          *  intros; apply Hg.
        }
        * apply: ex_RInt_comp'; eauto; try nra.
          { intros; apply Hh2cont. split; eapply Hmono; eauto; try nra. }
        * apply: ex_RInt_comp'; eauto; try nra.
          { intros; apply Hh1cont. split; eapply Hmono; eauto; try nra. }
      }
      rewrite ?RInt_comp'; eauto; try nra.
      {
        rewrite (is_RInt_unique _ _ _ _ His1).
        rewrite (is_RInt_unique _ _ _ _ His2).
        nra.
      }
      { intros. apply Hh2cont. split; eapply Hmono; eauto; try nra. }
      { intros. apply Hh1cont. split; eapply Hmono; eauto; try nra. }
Qed.

Lemma RInt_comp'_noncont  (f g dg : R → R) (a b : R):
  a <= b ->
  (ex_RInt f (g a) (g b)) ->
  (forall x y, a <= x /\ x <= y /\ y <= b -> g x <= g y) ->
  (∀ x : R, a <= x <= b → is_derive g x (dg x) ∧ continuous dg x) →
  RInt (λ y : R, scal (dg y) (f (g y))) a b = RInt f (g a) (g b).
Proof.
  intros.
  apply is_RInt_unique.
  apply is_RInt_comp_noncont; auto.
  { rewrite Rmin_left // Rmax_right //. }
  { rewrite Rmin_left // Rmax_right //. }
Qed.


End comp.
