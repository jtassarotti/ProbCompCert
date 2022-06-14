From Coq Require Import Reals Psatz ssreflect ssrbool Utf8.
From mathcomp Require Import eqtype seq.

From Coquelicot Require Import Markov Rcomplements Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive.
From Coquelicot Require Export Rbar.

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

Lemma RInt_upper_finite_UIRInt f a (b: R) :
  a < b ->
  ex_RInt f a b ->
  RInt f a b = UIRInt f a b.
Proof.
  intros. apply is_RInt_unique.
  apply is_RInt_upper_finite_UIRInt; auto.
  apply UIRInt_correct.
  apply ex_UIRInt_upper_finite_RInt; auto.
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

Lemma is_UIRInt_comp_noncont (f : R → R) (g dg : R → R) (a : R) (b : Rbar) (glim : Rbar) :
  Rbar_lt a b ->
  (forall (x y : R), Rbar_le a x /\ x <= y /\ Rbar_lt y b -> g x <= g y) ->
  (∀ (x : R), Rbar_le a x /\ Rbar_lt x b → is_derive g x (dg x) ∧ continuous dg x) →
  (* This should follow if g is is monotone locally to b *)
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glim) ->
  is_left_lim g b glim ->
  ex_UIRInt f (g a) glim ->
  is_UIRInt (fun y => scal (dg y) (f (g y))) a b (UIRInt f (g a) glim).
Proof.
  intros Hlt Hmono Hdiff Hatlt Hlim Hex.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  assert (Hltlim: ∀ r, a <= r -> Rbar_lt r b -> Rbar_lt (g r) glim).
  {
    intros t Hlt1 Hlt2.
    destruct b as [r' | |]; try (simpl in Hlt2; intuition).
    * edestruct (Rbar_at_left_witness_above r' t) as (z&Hz1&Hz2); eauto.
      eapply Rbar_le_lt_trans; last eapply Hz2.
      apply Hmono; simpl. nra.
    * edestruct (Rbar_at_left_witness_above_p_infty t) as (z&Hz1&Hz2); eauto.
      eapply Rbar_le_lt_trans; last eapply Hz2.
      apply Hmono; simpl. nra.
  }
  split.
  { intros t Hle1 Hlt2. eexists. apply: is_RInt_comp_noncont; auto.
    **  rewrite /ex_UIRInt in Hex. destruct Hex as (?&(Hex&?)). eapply Hex; eauto.
        { apply Hmono. split; auto. reflexivity. }
    ** intros x y. rewrite Rmin_left // Rmax_right //. intros. apply Hmono; try nra.
       simpl in Hlt2. intuition; simpl; try nra. destruct b; try eauto; try nra.
    ** intros x. rewrite Rmin_left // Rmax_right //. intros. apply Hdiff; try nra.
       split; first by (simpl; nra). simpl in Hlt2. simpl. destruct b; try intuition; nra.
  }
  eapply (is_left_lim_ext_loc (λ b, RInt f (g a) (g b))).
  {
    eapply Rbar_at_left_interval; eauto.
    intros x Hltx1 Hltx2.
    symmetry.
    assert (∃ r, x = Finite r) as (r&->).
    { destruct x, b; simpl in *; try intuition; try eexists; eauto. }
    simpl in Hltx1.
    apply RInt_comp'_noncont; auto.
    { apply Rlt_le. auto. }
    **  rewrite /ex_UIRInt in Hex. destruct Hex as (?&(Hex&?)). eapply Hex; eauto.
        { apply Hmono. split; auto. reflexivity. split; auto. clear -Hltx1. left. auto. }
    **  eapply Hltlim; eauto. left; auto.
    ** intros x y ?. apply Hmono; try nra.
       intuition; try done. eapply Rbar_le_lt_trans; eauto. simpl. auto.
    ** intros y (Hle1'&Hl2'). apply Hdiff.
       split; auto. eapply Rbar_le_lt_trans; eauto. simpl in *; eauto.
  }
  apply UIRInt_correct in Hex.
  destruct Hex as (?&Hlim').
  eapply (is_left_lim_comp (λ x, RInt f (g a) x) g b); eauto.
Qed.

Lemma UIRInt_comp_noncont (f : R → R) (g dg : R → R) (a : R) (b : Rbar) (glim : Rbar) :
  Rbar_lt a b ->
  (forall (x y : R), Rbar_le a x /\ x <= y /\ Rbar_lt y b -> g x <= g y) ->
  (∀ (x : R), Rbar_le a x /\ Rbar_lt x b → is_derive g x (dg x) ∧ continuous dg x) →
  (* This should follow if g is is monotone locally to b *)
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glim) ->
  is_left_lim g b glim ->
  ex_UIRInt f (g a) glim ->
  UIRInt (fun y => scal (dg y) (f (g y))) a b = UIRInt f (g a) glim.
Proof.
  intros. apply is_UIRInt_unique, is_UIRInt_comp_noncont; eauto.
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

Lemma is_UIRInt_lower_bound_right_lim : ∀ (a b : R) (f : R → R) (v : R),
    a < b → is_UIRInt f a b v → is_right_lim (λ x, UIRInt f x b) a (UIRInt f a b).
Proof.
Abort.

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

Lemma is_IRInt_finite_RInt_1 f (a b : R) v :
  Rbar_lt a b ->
  is_RInt f a b v -> is_IRInt f a b v.
Proof.
  intros Hlt His. split.
  * intros t Hle1 Hl2.
    apply: (ex_UIRInt_Chasles_1 _ _ b).
    { split; first eauto.  reflexivity. }
    { eapply (ex_UIRInt_Chasles_2 f a); eauto.
      { split; auto. apply Rbar_lt_le. auto. }
      eapply ex_UIRInt_upper_finite_RInt; eauto.
      eexists; eauto. }
  * rewrite -(is_RInt_unique _ _ _ _ His).
    eapply is_right_lim_ext_loc; last eapply is_RInt_lower_bound_right_lim; eauto.
    eapply Rbar_at_right_interval; eauto.
    unfold Rbar_lt. intros [r| |]; simpl; try intuition. eapply RInt_upper_finite_UIRInt; eauto.
    eapply ex_RInt_Chasles_2; last by (eexists; eauto).
    nra.
Qed.

Lemma is_RInt_finite_IRInt f a (b: R) v :
  a < b ->
  ex_RInt f a b ->
  is_IRInt f a b v -> is_RInt f a b v.
Proof.
  intros Hlt (v'&His) Hisu.
  cut (v = v').
  { intros ->. auto. }
  eapply is_IRInt_finite_RInt_1 in His; auto.
  apply is_IRInt_unique in His.
  apply is_IRInt_unique in Hisu.
  congruence.
Qed.

Lemma is_IRInt_comp (f : R → R) (g dg : R → R) (a b : Rbar) (gla glb : Rbar) :
  Rbar_lt a b ->
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → Rbar_lt gla (g x) /\ Rbar_lt (g x) glb) →
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → continuous f (g x)) →
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → is_derive g x (dg x) ∧ continuous dg x) →
  (* This should follow if g is is monotone locally to a and b *)
  Rbar_at_right a (λ y : Rbar, Rbar_lt gla (g y)) ->
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glb) ->
  is_right_lim g a gla ->
  is_left_lim g b glb ->
  ex_IRInt f gla glb ->
  is_IRInt (fun y => scal (dg y) (f (g y))) a b (IRInt f gla glb).
Proof.
  intros Hlt Hgrange Hcontinuous Hdiff Hata Hatb Hlima Hlimb Hex.
  rewrite /ex_IRInt/is_IRInt/IRInt.
  split.
  { intros t Hlt1 Hlt2. eexists. apply: is_UIRInt_comp; eauto.
    ** intros x (Hle1'&Hlt2'). apply Hcontinuous.
       split; auto. eapply Rbar_lt_le_trans; eauto.
    ** intros x. intros (Hle1'&Hlt2'). apply Hdiff.
       split; auto. eapply Rbar_lt_le_trans; eauto.
    ** destruct Hex as (?&Hex'&?). eapply Hex'; eauto; eapply Hgrange; eauto.
  }
  eapply (is_right_lim_ext_loc (λ r, UIRInt f (g r) glb)).
  {
    eapply Rbar_at_right_interval; eauto.
    intros x Hltx1 Hltx2.
    symmetry.
    assert (∃ r, x = Finite r) as (r&->).
    { destruct x, a, b; simpl in *; try intuition; try eexists; eauto. }
    erewrite UIRInt_comp; eauto.
    ** intros y (Hle1'&Hl2'). apply Hcontinuous.
       split; auto. eapply Rbar_lt_le_trans; eauto.
    ** intros y (Hle1'&Hl2'). apply Hdiff.
       split; auto. eapply Rbar_lt_le_trans; eauto.
    ** destruct Hex as (?&Hex'&?). eapply Hex'; eauto; eapply Hgrange; eauto.
  }
  apply IRInt_correct in Hex.
  destruct Hex as (?&Hlim').
  eapply (is_right_lim_comp (λ x, UIRInt f x glb) g a); eauto.
Qed.

Lemma is_IRInt_comp_noncont (f : R → R) (g dg : R → R) (a b : Rbar) (gla glb : Rbar) :
  Rbar_lt a b ->
  (∀ (x y : R), Rbar_lt a x /\ x <= y /\ Rbar_lt y b -> g x <= g y) ->
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → Rbar_lt gla (g x) /\ Rbar_lt (g x) glb) →
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → is_derive g x (dg x) ∧ continuous dg x) →
  (* This should follow if g is is monotone locally to a and b *)
  Rbar_at_right a (λ y : Rbar, Rbar_lt gla (g y)) ->
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glb) ->
  is_right_lim g a gla ->
  is_left_lim g b glb ->
  ex_IRInt f gla glb ->
  is_IRInt (fun y => scal (dg y) (f (g y))) a b (IRInt f gla glb).
Proof.
  intros Hlt Hmono Hgrange Hdiff Hata Hatb Hlima Hlimb Hex.
  rewrite /ex_IRInt/is_IRInt/IRInt.
  split.
  { intros t Hlt1 Hlt2. eexists. apply: is_UIRInt_comp_noncont; eauto.
    ** intros x y (Hle1'&Hle2'&Hlt3'). apply Hmono.
       split; auto. eapply Rbar_lt_le_trans; eauto.
    ** intros x. intros (Hle1'&Hlt2'). apply Hdiff.
       split; auto. eapply Rbar_lt_le_trans; eauto.
    ** destruct Hex as (?&Hex'&?). eapply Hex'; eauto; eapply Hgrange; eauto.
  }
  eapply (is_right_lim_ext_loc (λ r, UIRInt f (g r) glb)).
  {
    eapply Rbar_at_right_interval; eauto.
    intros x Hltx1 Hltx2.
    symmetry.
    assert (∃ r, x = Finite r) as (r&->).
    { destruct x, a, b; simpl in *; try intuition; try eexists; eauto. }
    erewrite UIRInt_comp_noncont; eauto.
    ** intros x y (Hle1'&Hle2'&Hlt3'). apply Hmono.
       split; auto. eapply Rbar_lt_le_trans; eauto.
    ** intros y (Hle1'&Hl2'). apply Hdiff.
       split; auto. eapply Rbar_lt_le_trans; eauto.
    ** destruct Hex as (?&Hex'&?). eapply Hex'; eauto; eapply Hgrange; eauto.
  }
  apply IRInt_correct in Hex.
  destruct Hex as (?&Hlim').
  eapply (is_right_lim_comp (λ x, UIRInt f x glb) g a); eauto.
Qed.

Lemma IRInt_comp (f : R → R) (g dg : R → R) (a b : Rbar) (gla glb : Rbar) :
  Rbar_lt a b ->
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → Rbar_lt gla (g x) /\ Rbar_lt (g x) glb) →
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → continuous f (g x)) →
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → is_derive g x (dg x) ∧ continuous dg x) →
  (* This should follow if g is is monotone locally to a and b *)
  Rbar_at_right a (λ y : Rbar, Rbar_lt gla (g y)) ->
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glb) ->
  is_right_lim g a gla ->
  is_left_lim g b glb ->
  ex_IRInt f gla glb ->
  IRInt (fun y => scal (dg y) (f (g y))) a b = (IRInt f gla glb).
Proof.
  intros. apply is_IRInt_unique, is_IRInt_comp; eauto.
Qed.

Lemma IRInt_comp_noncont (f : R → R) (g dg : R → R) (a b : Rbar) (gla glb : Rbar) :
  Rbar_lt a b ->
  (∀ (x y : R), Rbar_lt a x /\ x <= y /\ Rbar_lt y b -> g x <= g y) ->
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → Rbar_lt gla (g x) /\ Rbar_lt (g x) glb) →
  (∀ (x : R), Rbar_lt a x /\ Rbar_lt x b → is_derive g x (dg x) ∧ continuous dg x) →
  (* This should follow if g is is monotone locally to a and b *)
  Rbar_at_right a (λ y : Rbar, Rbar_lt gla (g y)) ->
  Rbar_at_left b (λ y : Rbar, Rbar_lt (g y) glb) ->
  is_right_lim g a gla ->
  is_left_lim g b glb ->
  ex_IRInt f gla glb ->
  IRInt (fun y => scal (dg y) (f (g y))) a b = (IRInt f gla glb).
Proof.
  intros. apply is_IRInt_unique, is_IRInt_comp_noncont; eauto.
Qed.

End IRInt.

Require Import Coquelicot.AutoDerive.

Lemma LowerBound_reparam_lb_right_lim a : is_right_lim (λ y : R, exp y + a) m_infty a.
Proof.
  replace a with (0 + a) at 1; last nra.
  apply (is_right_lim_plus' exp (λ _, a)).
  * apply is_lim_right_lim; first congruence.
    apply ElemFct.is_lim_exp_m.
  * apply is_right_lim_const; congruence.
Qed.

Lemma LowerBound_reparam_ub_left_lim a : is_left_lim (λ y : R, exp y + a) p_infty p_infty.
Proof.
  apply (is_left_lim_plus exp (λ _, a) p_infty p_infty a p_infty).
  { apply is_lim_left_lim; first congruence.
    apply ElemFct.is_lim_exp_p. }
  { apply is_left_lim_const; congruence. }
  constructor.
Qed.

Lemma LowerBounded_reparam_full f a  :
  (∀ (x : R), a < x → continuous f x) →
  ex_IRInt f a p_infty ->
  is_IRInt (fun y => exp y * f (exp(y) + a)) m_infty p_infty (IRInt f a p_infty).
Proof.
  intros Hcont Hex.
  apply (is_IRInt_comp f (λ x, exp x + a) exp); try (done).
  - intros x Hrange0. simpl. split; auto. cut (0 < exp x); first nra. apply exp_pos.
  - intros x Hrange0. simpl. apply Hcont. cut (0 < exp x); first nra. apply exp_pos.
  - intros x Hrange0. split.
    { auto_derive; auto; nra. }
    { apply ElemFct.continuous_exp. }
  - apply (Rbar_at_right_strict_monotone a m_infty (λ y, exp y + a)); try done.
    { intros x y (?&?) Hltm. cut (exp x < exp y); first by nra.
      by apply exp_increasing. }
    apply LowerBound_reparam_lb_right_lim.
  - apply (Rbar_at_left_strict_monotone a p_infty (λ y, exp y + a)); try done.
    { intros x y (?&?) Hltm. cut (exp x < exp y); first by nra.
      by apply exp_increasing. }
    apply LowerBound_reparam_ub_left_lim.
  - apply LowerBound_reparam_lb_right_lim.
  - apply LowerBound_reparam_ub_left_lim.
Qed.
