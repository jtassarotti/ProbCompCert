From Coq Require Import Reals Psatz ssreflect ssrbool Utf8.
From mathcomp Require Import eqtype seq.

From Coquelicot Require Import Markov Rcomplements Rbar Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive.

Require Import RealsExt.

Section Upper_IRInt.

Context {V : CompleteNormedModule R_AbsRing}.

Definition is_finite_dec (x : Rbar) : { is_finite x } + {~ is_finite x}.
Proof.
  destruct x.
  - left; econstructor; eauto.
  - right; inversion 1.
  - right; inversion 1.
Defined.

Definition is_UIRInt (f: R -> R) (a: R) (b: Rbar) (If: R) :=
  (forall (t : R), Rle a t -> Rbar_lt t b -> ex_RInt f a t) /\ is_left_lim (RInt f a) b If.

Definition ex_UIRInt (f : R -> R) (a: R) (b : Rbar) :=
  exists If : R, is_UIRInt f a b If.

Definition UIRInt (f: R -> R) (a : R) (b : Rbar) : R :=
  real (LeftLim (RInt f a) b).

Lemma UIRInt_correct f a b :
  ex_UIRInt f a b -> is_UIRInt f a b (UIRInt f a b).
Proof.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  intros (v&Hex&Hlim).
  split; first done.
  rewrite /UIRInt.
  apply LeftLim_correct'. econstructor; eauto.
Qed.

Lemma is_UIRInt_unique f a b v :
  is_UIRInt f a b v -> UIRInt f a b = v.
Proof.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  intros (Hex&His). rewrite /UIRInt.
  erewrite is_left_lim_unique; eauto. simpl; done.
Qed.

Lemma is_UIRInt_upper_finite_RInt_1 f a (b: R) v :
  a < b ->
  is_RInt f a b v -> is_UIRInt f a b v.
Proof.
  intros Hlt His. split.
  * intros t Hle1 Hl2. apply: (ex_RInt_Chasles_1 _ _ _ b); eauto.
    { split; first eauto. simpl in Hl2. nra. }
    { econstructor; eauto. }
  * rewrite -(is_RInt_unique _ _ _ _ His).
    apply: is_RInt_upper_bound_left_lim; eauto.
Qed.

Lemma is_RInt_upper_finite_UIRInt f a (b: R) v :
  a < b ->
  ex_RInt f a b ->
  is_UIRInt f a b v -> is_RInt f a b v.
Proof.
  intros Hlt (v'&His) Hisu.
  cut (v = v').
  { intros ->. auto. }
  eapply is_UIRInt_upper_finite_RInt_1 in His; auto.
  apply is_UIRInt_unique in His.
  apply is_UIRInt_unique in Hisu.
  congruence.
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


Set Nested Proofs Allowed.
Lemma interval_inhabited (x y : R) : x < y -> ∃ z, x < z < y.
Proof.
  intros.
  edestruct (boule_of_interval x y) as (s&(r&Heq1&Heq2)); auto.
  exists s. nra.
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
  (∀ x y, t <= x < y → Rbar_lt y b → g x < g y) →
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
      rewrite Heq. simpl. apply Ht; auto; split; try nra.
    }
    apply open_Rbar_lt' in r0. apply Hlim in r0.
    eapply (Rbar_at_left_witness_above_p_infty x) in r0; try (intuition eauto; done).
    destruct r0 as (y&Hrange'&Hlt).
    simpl in Hlt. apply Rlt_not_le in Hlt.
    apply Hlt. left. apply Ht; simpl; simpl in Hltb; try nra.
Qed.

Lemma is_UIRInt_comp (f : R → R) (g dg : R → R) (a : R) (b : Rbar) (glim : Rbar) :
  Rbar_lt a b ->
  (∀ (x : R), Rbar_le a x /\ Rbar_lt x b → continuous f (g x)) →
  (∀ (x : R), Rbar_le a x /\ Rbar_lt x b → is_derive g x (dg x) ∧ continuous dg x) →
  (* This should follow if g is is monotone locally to b *)
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glim) ->
  is_left_lim g b glim ->
  ex_UIRInt f (g a) glim ->
  is_UIRInt (fun y => scal (dg y) (f (g y))) a b (UIRInt f (g a) glim).
Proof.
  intros Hlt Hcontinuous Hdiff Hatlt Hlim Hex.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  split.
  { intros t Hle1 Hlt2. eexists. apply: is_RInt_comp'; auto.
    ** intros x (Hle1'&Hl2'). apply Hcontinuous.
       split; auto. simpl in Hlt2. simpl. destruct b; try eauto. nra.
    ** intros x. intros (Hle1'&Hl2'). apply Hdiff.
       split; auto. simpl in Hlt2. simpl. destruct b; try eauto. nra.
  }
  eapply (is_left_lim_ext_loc (λ b, RInt f (g a) (g b))).
  {
    eapply Rbar_at_left_interval; eauto.
    intros x Hltx1 Hltx2.
    symmetry.
    assert (∃ r, x = Finite r) as (r&->).
    { destruct x, b; simpl in *; try intuition; try eexists; eauto. }
    simpl in Hltx1.
    apply RInt_comp'; auto.
    { apply Rlt_le. auto. }
    ** intros y (Hle1'&Hl2'). apply Hcontinuous.
       split; auto. eapply Rbar_le_lt_trans; eauto. simpl in *; eauto.
    ** intros y (Hle1'&Hl2'). apply Hdiff.
       split; auto. eapply Rbar_le_lt_trans; eauto. simpl in *; eauto.
  }
  apply UIRInt_correct in Hex.
  destruct Hex as (?&Hlim').
  eapply (is_left_lim_comp (λ x, RInt f (g a) x) g b); eauto.
Qed.

End Upper_IRInt.
