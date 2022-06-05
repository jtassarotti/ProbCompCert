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
  match is_finite_dec b with
  | left _ => is_RInt f a (real b) If
  | _ => (forall t, Rle a t -> Rbar_le t b -> ex_RInt f a t) /\ is_lim (RInt f a) b If
  end.

Definition ex_UIRInt (f : R -> R) (a: R) (b : Rbar) :=
  exists If : R, is_UIRInt f a b If.

Definition UIRInt (f: R -> R) (a : R) (b : Rbar) : R :=
  match is_finite_dec b with
  | left _ => RInt f a (real b)
  | _ => real (Lim (RInt f a) b)
  end.

Lemma UIRInt_correct f a b :
  ex_UIRInt f a b -> is_UIRInt f a b (UIRInt f a b).
Proof.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  destruct (is_finite_dec b).
  - intros. apply: RInt_correct; auto.
  - intros (v&Hex&Hlim).
    split; first done.
    rewrite /UIRInt.
    apply Lim_correct'. econstructor; eauto.
Qed.

Lemma is_UIRInt_unique f a b v :
  is_UIRInt f a b v -> UIRInt f a b = v.
Proof.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  destruct (is_finite_dec b).
  - apply: is_RInt_unique.
  - intros (Hex&His). rewrite /UIRInt.
    erewrite is_lim_unique; eauto. simpl; done.
Qed.

Lemma is_UIRInt_upper_finite_RInt f a (b: R) v :
  is_RInt f a b v -> is_UIRInt f a b v.
Proof. rewrite /is_UIRInt. intros His => /=. auto. Qed.

Lemma is_RInt_upper_finite_UIRInt f a (b: R) v :
  is_UIRInt f a b v -> is_RInt f a b v.
Proof. rewrite /is_UIRInt/=//. Qed.

Lemma is_UIRInt_comp0 (f : R → R) (g dg : R → R) (a b : R):
  a < b ->
  (∀ x : R, a <= x → continuous f (g x)) ->
  (∀ x : R, a <= x → is_derive g x (dg x) ∧ continuous dg x) ->
  is_lim g p_infty b ->
  is_UIRInt (fun y => scal (dg y) (f (g y))) a p_infty (UIRInt f (g a) b).
Proof.
  intros Hlt Hcontinuous Hdiff Hlim.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  rewrite /=.
  assert (forall t, a <= t ->
            is_RInt (λ y, scal (dg y) (f (g y))) a t (RInt f (g a) (g t))).
  {
    intros t Hrange. apply: is_RInt_comp; auto.
    { intros x.
      rewrite Rmin_left ?Rmax_right; try (intuition eauto; done).
    }
    { intros x.
      rewrite Rmin_left ?Rmax_right; try (intuition eauto; done).
      intros. eapply Hdiff; nra.
    }
  }
  split.
  { intros; eexists; eauto. }
Abort.

Lemma is_UIRInt_comp1 (f : R → R) (g dg : R → R) (a : R) (b : R):
  a < b ->
  (∀ x : R, a <= x ∧ x < b → continuous f (g x)) ->
  (∀ x : R, a <= x ∧ x < b → is_derive g x (dg x) ∧ continuous dg x) ->
  is_lim g b p_infty ->
  is_UIRInt (fun y => scal (dg y) (f (g y))) a b (UIRInt f (g a) p_infty).
Proof.
  intros Hlt Hcontinuous Hdiff Hlim.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  rewrite /=.
  assert (forall t, a <= t /\ t < b ->
            is_RInt (λ y, scal (dg y) (f (g y))) a t (RInt f (g a) (g t))).
  {
    intros t Hrange. apply: is_RInt_comp; auto.
    { intros x.
      rewrite Rmin_left ?Rmax_right; try (intuition eauto; done).
      intros. eapply Hcontinuous. split; nra.
    }
    { intros x.
      rewrite Rmin_left ?Rmax_right; try (intuition eauto; done).
      intros. eapply Hdiff. split; nra.
    }
  }
Abort.

Lemma continuous_left_is_RInt (f : R -> R) a b v g :
  a < b ->
  (∀ t, a <= t <= b -> is_RInt f a t (g t)) ->
  is_lim (λ x, g (Rmin x b)) b v ->
  is_RInt f a b v.
Proof.
Abort.

Lemma is_UIRInt_comp1 (f : R → R) (g dg : R → R) (a : R) (b : R) glim :
  a < b ->
  (∀ x : R, a <= x ∧ x < b → continuous f (g x)) ->
  (∀ x : R, a <= x ∧ x < b → is_derive g x (dg x) ∧ continuous dg x) ->
  is_lim g b glim ->
  is_UIRInt (fun y => scal (dg y) (f (g y))) a b (UIRInt f (g a) glim).
Proof.
Abort.
(*
  intros Hlt Hcontinuous Hdiff Hlim.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  rewrite /=.
  destruct (is_finite_dec glim) as [Hfin|Hnfin].
  {
    destruct glim; inversion Hfin; [].
    assert (r = g b) as ->.
    { eapply is_lim_unique'_R; eauto.
      apply is_lim_continuity'; auto.
      apply: filterdiff_continuous.
      eexists. eapply Hdiff; eauto.
      split; auto using Rmin_r, Rmax_r.
    }
    apply (is_RInt_comp f g dg a b); eauto.
  }
  intor
  destruct (is_finite_dec b).
  {
    * simpl.
  split.
  * intros t Hle Hle2.
    eexists. apply: is_RInt_comp.
    ** intros x (Hle1'&Hle2'). apply Hcontinuous; split; auto.
       *** etransitivity; first apply Rbar_min_l. simpl. rewrite Rmin_left in Hle1'; auto.
       ***
Abort.



Lemma is_UIRInt_comp1 (f : R → R) (g dg : R → R) (a : R) (b : R) glim :
  (∀ x : R, Rmin a b <= x ∧ x <= Rmax a b → continuous f (g x)) ->
  (∀ x : R, Rmin a b <= x ∧ x <= Rmax a b → is_derive g x (dg x) ∧ continuous dg x) ->
  is_lim g b glim ->
  is_UIRInt (fun y => scal (dg y) (f (g y))) a b (UIRInt f (g a) glim).
Proof.
  intros Hcontinuous Hdiff Hlim.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  rewrite /=.
  destruct (is_finite_dec glim) as [Hfin|Hnfin].
  {
    destruct glim; inversion Hfin; [].
    assert (r = g b) as ->.
    { eapply is_lim_unique'_R; eauto.
      apply is_lim_continuity'; auto.
      apply: filterdiff_continuous.
      eexists. eapply Hdiff; eauto.
      split; auto using Rmin_r, Rmax_r.
    }
    apply (is_RInt_comp f g dg a b); eauto.
  }
  Search is_RInt.
  intor
  destruct (is_finite_dec b).
  {
    * simpl.
  split.
  * intros t Hle Hle2.
    eexists. apply: is_RInt_comp.
    ** intros x (Hle1'&Hle2'). apply Hcontinuous; split; auto.
       *** etransitivity; first apply Rbar_min_l. simpl. rewrite Rmin_left in Hle1'; auto.
       ***
Abort.




Lemma is_UIRInt_comp (f : R → R) (g dg : R → R) (a : R) (b : Rbar) :
  (∀ (x : R), Rbar_le (Rbar_min a b) x /\ Rbar_le x (Rbar_max a b) → continuous f (g x)) →
  (∀ (x : R), Rbar_le (Rbar_min a b) x /\ Rbar_le x (Rbar_max a b) → is_derive g x (dg x) ∧ continuous dg x) →
  is_UIRInt (fun y => scal (dg y) (f (g y))) a b (UIRInt f (g a) (g b)).
Proof.
  intros Hcontinuous Hdiff.
  rewrite /ex_UIRInt/is_UIRInt/UIRInt.
  destruct (is_finite_dec b).
  {
    * simpl.
  split.
  * intros t Hle Hle2.
    eexists. apply: is_RInt_comp.
    ** intros x (Hle1'&Hle2'). apply Hcontinuous; split; auto.
       *** etransitivity; first apply Rbar_min_l. simpl. rewrite Rmin_left in Hle1'; auto.
       ***
Abort.
*)

End Upper_IRInt.
