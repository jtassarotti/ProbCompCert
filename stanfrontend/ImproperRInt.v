From Coq Require Import Reals Psatz ssreflect ssrbool Utf8.
From mathcomp Require Import eqtype seq.

From Coquelicot Require Import Markov Rcomplements Rbar Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive.

Require Import RealsExt.

Section Upper_IRInt.

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

Lemma ex_UIRInt_upper_finite_RInt f a (b: R) :
  a < b ->
  ex_RInt f a b -> ex_UIRInt f a b.
Proof. intros ? (?&?). eexists. eapply is_UIRInt_upper_finite_RInt_1; eauto. Qed.

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

Lemma ex_UIRInt_Chasles_1
  : ∀ f (a : R) (b c : Rbar), Rbar_lt a b ∧ Rbar_le b c → ex_UIRInt f a c → ex_UIRInt f a b.
Proof.
  intros f a b c (Hle1&Hle2) Hex.
  destruct (Rbar_le_lt_or_eq_dec b c) as [Hlt|Heq]; eauto; last first.
  { subst. eauto. }
  destruct b as [r | |]; try (simpl in Hle1, Hlt; intuition; done).
  apply ex_UIRInt_upper_finite_RInt; auto.
  destruct Hex as (v&His).
  destruct His as (Hex&Hlim).
  apply Hex; eauto. simpl in Hle1. nra.
Qed.

Lemma ex_UIRInt_Chasles_2
  : ∀ f (a b : R)  (c : Rbar), Rbar_le a b ∧ Rbar_lt b c → ex_UIRInt f a c → ex_UIRInt f b c.
Proof.
  intros f a b c (Hle1&Hle2) Hex.
  destruct (Rbar_le_lt_or_eq_dec a b) as [Hlt|Heq]; eauto; last first.
  { inversion Heq; subst. eauto. }
  destruct Hex as (v&His).
  destruct His as (Hex&Hlim).
  exists (v + (-RInt f a b)). split.
  { intros. apply: ex_RInt_Chasles_2; eauto. eapply Hex; eauto. simpl in Hle1. etransitivity; eauto. }
  eapply (is_left_lim_ext_loc (λ x, RInt f a x + (-RInt f a b))).
  { eapply Rbar_at_left_interval; eauto. intros x Hlt1 Hlt2.
    rewrite -(RInt_Chasles f a b x).
    { rewrite /plus//=. nra. }
    { eapply Hex; eauto. }
    { destruct x as [x' | |]; try (simpl in Hlt1, Hlt2; try intuition; done).
      apply: ex_RInt_Chasles_2; try eapply Hex; eauto.
       { simpl in Hle1, Hlt1. split; simpl; try nra. }
       simpl in Hlt, Hlt1. simpl. nra. }
  }
  apply is_left_lim_plus'; auto.
  apply is_left_lim_const. intros ->. apply Hle2.
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

Lemma UIRInt_comp (f : R → R) (g dg : R → R) (a : R) (b : Rbar) (glim : Rbar) :
  Rbar_lt a b ->
  (∀ (x : R), Rbar_le a x /\ Rbar_lt x b → continuous f (g x)) →
  (∀ (x : R), Rbar_le a x /\ Rbar_lt x b → is_derive g x (dg x) ∧ continuous dg x) →
  (* This should follow if g is is monotone locally to b *)
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glim) ->
  is_left_lim g b glim ->
  ex_UIRInt f (g a) glim ->
  UIRInt (fun y => scal (dg y) (f (g y))) a b = UIRInt f (g a) glim.
Proof.
  intros. apply is_UIRInt_unique, is_UIRInt_comp; eauto.
Qed.

End Upper_IRInt.

Section IRInt.

Definition is_IRInt (f: R -> R) (a: Rbar) (b: Rbar) (If: R) :=
  (forall (t : R), Rbar_lt a t -> Rbar_lt t b -> ex_UIRInt f t b) /\ is_right_lim (λ x, UIRInt f x b) a If.

Definition ex_IRInt (f : R -> R) (a: Rbar) (b : Rbar) :=
  exists If : R, is_IRInt f a b If.

Definition IRInt (f: R -> R) (a : Rbar) (b : Rbar) : R :=
  real (RightLim (λ x, UIRInt f x b) a).

Lemma IRInt_correct f a b :
  ex_IRInt f a b -> is_IRInt f a b (IRInt f a b).
Proof.
  rewrite /ex_IRInt/is_IRInt/IRInt.
  intros (v&Hex&Hlim).
  split; first done.
  apply RightLim_correct'. econstructor; eauto.
Qed.

Lemma is_IRInt_unique f a b v :
  is_IRInt f a b v -> IRInt f a b = v.
Proof.
  rewrite /ex_IRInt/is_IRInt/IRInt.
  intros (Hex&His).
  erewrite is_right_lim_unique; eauto. simpl; done.
Qed.

Lemma is_IRInt_lower_finite_UIRInt_1 f (a : R) (b: Rbar) v :
  Rbar_lt a b ->
  is_UIRInt f a b v -> is_IRInt f a b v.
Proof.
  intros Hlt His. split.
  * intros t Hle1 Hl2.
    apply: (ex_UIRInt_Chasles_1 _ _ b).
    { split; first eauto.  reflexivity. }
    { eapply (ex_UIRInt_Chasles_2 f a); eauto.
      { split; auto. apply Rbar_lt_le. auto. }
      eexists; eauto. }
  * rewrite -(is_UIRInt_unique _ _ _ _ His).
Abort.
(*
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

Lemma UIRInt_comp (f : R → R) (g dg : R → R) (a : R) (b : Rbar) (glim : Rbar) :
  Rbar_lt a b ->
  (∀ (x : R), Rbar_le a x /\ Rbar_lt x b → continuous f (g x)) →
  (∀ (x : R), Rbar_le a x /\ Rbar_lt x b → is_derive g x (dg x) ∧ continuous dg x) →
  (* This should follow if g is is monotone locally to b *)
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glim) ->
  is_left_lim g b glim ->
  ex_UIRInt f (g a) glim ->
  UIRInt (fun y => scal (dg y) (f (g y))) a b = UIRInt f (g a) glim.
Proof.
  intros. apply is_UIRInt_unique, is_UIRInt_comp; eauto.
Qed.
*)

End IRInt.
