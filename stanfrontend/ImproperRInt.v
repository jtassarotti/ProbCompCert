From Coq Require Import Reals Psatz ssreflect ssrbool Utf8.
From mathcomp Require Import eqtype seq.

From Coquelicot Require Import Markov Rcomplements Rbar Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive.

Require Import RealsExt.

Section Upper_IRInt.

Context {V : CompleteNormedModule R_AbsRing}.

Definition is_UIRInt (f: R -> R) (a: R) (b: Rbar) (If: R) :=
  (forall t, Rle a t -> Rbar_le t b -> ex_RInt f a t) /\
  is_lim (RInt f a) b If.

Definition ex_UIRInt (f : R -> R) (a: R) (b : Rbar) :=
  exists If : R, is_UIRInt f a b If.

Definition UIRInt (f: R -> R) (a : R) (b : Rbar) : R :=
  real (Lim (RInt f a) b).

Lemma UIRInt_correct f a b :
  ex_UIRInt f a b -> is_UIRInt f a b (UIRInt f a b).
Proof.
  intros (v&Hex&Hlim).
  split; first done.
  rewrite /UIRInt.
  apply Lim_correct'. econstructor; eauto.
Qed.

Lemma is_UIRInt_unique f a b v :
  is_UIRInt f a b v -> UIRInt f a b = v.
Proof.
  intros (Hex&His). rewrite /UIRInt.
  erewrite is_lim_unique; eauto. simpl; done.
Qed.

Lemma is_UIRInt_upper_finite_RInt_1 f a (b: R) v :
  a < b ->
  (exists eps : posreal, ex_RInt f a (b + eps)) ->
  is_RInt f a b v -> is_UIRInt f a b v.
Proof.
  intros Hle Hex His. split.
  * intros t Hle1 Hl2. apply: ex_RInt_Chasles_1; eauto.
    { econstructor; eauto. }
  * rewrite -(is_RInt_unique _ _ _ _ His).
    apply is_lim_continuity.
    destruct Hex as (eps&Hex).
    unfold locally.
    apply continuity_pt_filterlim.
    apply (continuous_RInt_1 f a b _).
    destruct (eps_squeeze_between a b eps) as (eps'&Heps'); auto.
    exists eps'. rewrite /ball/=/AbsRing_ball.
    intros; apply: RInt_correct; auto.
    apply: ex_RInt_Chasles_1; eauto.
Qed.

Lemma is_UIRInt_upper_finite_RInt_2 f a (b: R) v :
  (forall x y, ex_RInt f x y) ->
  is_RInt f a b v -> is_UIRInt f a b v.
Proof.
  intros Hint His. split.
  * auto.
  * rewrite -(is_RInt_unique _ _ _ _ His).
    apply is_lim_continuity.
    unfold locally.
    apply continuity_pt_filterlim.
    apply (continuous_RInt_1 f a b _).
    exists posreal_one.
    intros; apply: RInt_correct; auto.
Qed.

Lemma is_RInt_upper_finite_UIRInt f a (b: R) v :
  (forall x y, ex_RInt f x y) ->
  is_UIRInt f a b v -> is_RInt f a b v.
Proof.
  intros Hint His.
  destruct His as (?&His).
  cut (RInt f a b = v).
  { intros <-. apply: RInt_correct; auto. }
  eapply is_lim_unique'_R; last eauto.
  apply is_lim_continuity.
  unfold locally.
  apply continuity_pt_filterlim.
  apply (continuous_RInt_1 f a b _).
  exists posreal_one.
  intros; apply: RInt_correct; auto.
Qed.

(* Stated almost exactly as is_RInt_comp *)
Lemma is_UIRInt_comp (f : R → R) (g dg : R → R) (a : R) (b : Rbar) :
  (∀ (x : R), Rbar_le (Rbar_min a b) x /\ Rbar_le x (Rbar_max a b) → continuous f (g x)) →
  (∀ (x : R), Rbar_le (Rbar_min a b) x /\ Rbar_le x (Rbar_max a b) → is_derive g x (dg x) ∧ continuous dg x) →
  is_UIRInt (fun y => scal (dg y) (f (g y))) a b (UIRInt f (g a) (g b)).
Proof.
  intros Hcontinuous Hdiff.
  split.
  * intros t Hle Hle2.
    eexists. apply: is_RInt_comp.
    ** intros x (Hle1'&Hle2'). apply Hcontinuous; split; auto.
       *** etransitivity; first apply Rbar_min_l. simpl. rewrite Rmin_left in Hle1'; auto.
       ***
Abort.

End Upper_IRInt.
