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
  { intros t Hle1 Hlt2. eexists. apply: is_RInt_comp.
    ** intros x. rewrite Rmin_left; auto. rewrite Rmax_right; auto. intros (Hle1'&Hl2'). apply Hcontinuous.
       split; auto. simpl in Hlt2. simpl. destruct b; try eauto. nra.
    ** intros x. rewrite Rmin_left; auto. rewrite Rmax_right; auto. intros (Hle1'&Hl2'). apply Hdiff.
       split; auto. simpl in Hlt2. simpl. destruct b; try eauto. nra.
  }
  eapply (is_left_lim_ext_loc (λ b, RInt f (g a) (g b))).
  {
    eapply Rbar_at_left_interval; eauto.
    intros x Hltx1 Hltx2.
    symmetry.
    assert (∃ r, x = Finite r) as (r&->).
    { destruct x, b; simpl in *; try intuition; try eexists; eauto. }
    apply: RInt_comp.
    ** intros y.
       rewrite Rmin_left; last first.
       { simpl in *; nra. }
       rewrite Rmax_right; last first.
       { simpl in *; nra. }
       intros (Hle1'&Hl2'). apply Hcontinuous.
       split; auto.
       { eapply Rbar_le_lt_trans; eauto. simpl in *; eauto. }
    ** intros y.
       rewrite Rmin_left; last first.
       { simpl in *; nra. }
       rewrite Rmax_right; last first.
       { simpl in *; nra. }
       intros (Hle1'&Hl2'). apply Hdiff.
       split; auto.
       { eapply Rbar_le_lt_trans; eauto. simpl in *; eauto. }
  }
  apply UIRInt_correct in Hex.
  destruct Hex as (?&Hlim').
  eapply (is_left_lim_comp (λ x, RInt f (g a) x) g b); eauto.
Qed.

End Upper_IRInt.
