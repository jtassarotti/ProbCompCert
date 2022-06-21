From Coq Require Import Reals Psatz ssreflect ssrbool Utf8 Vector.
From mathcomp Require Import eqtype seq.
Require Import Coq.Program.Equality.
From Coquelicot Require Import Markov Rcomplements Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive.
From Coquelicot Require Export Rbar.

Require Import RealsExt ImproperRInt.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Ltac sigT_inj :=
  repeat match goal with
  | [ H: existT _ _ _ = existT _ _ _ |- _ ] =>
    apply Classical_Prop.EqdepTheory.inj_pair2 in H; subst
  end.

Record interval := mk_interval { interval_lb : Rbar; interval_ub : Rbar}.

Definition interval_subset (i1 i2: interval) :=
  Rbar_le (interval_lb i2) (interval_lb i1) /\ Rbar_le (interval_ub i1) (interval_ub i2).

Definition rectangle n := Vector.t (interval) n.
Definition vsingle {A: Type} (a: A) :=
  cons A a O (nil A).
Definition in_interval (x: R) (i: interval) :=
  Rbar_lt (interval_lb i) x /\ Rbar_lt x (interval_ub i).
Definition in_rectangle {n: nat} (x: Vector.t _ n) (r: rectangle n) :=
  Forall2 in_interval x r.

Definition wf_interval (i: interval) :=
  Rbar_lt (interval_lb i) (interval_ub i).
Definition wf_rectangle (n: nat) (v: rectangle n) :=
  VectorDef.Forall wf_interval v.

Definition IIRInt (n: nat) (f: Vector.t R n -> R) (r: rectangle n) : R.
Proof.
  destruct n as [| n].
  - exact 0.
  - induction n as [| n' IH].
    { inversion r.
      exact (IRInt (λ x, f (vsingle x)) (interval_lb h) (interval_ub h)).
    }
    { inversion r.
      exact (IRInt (λ x, IH (λ xbar, f (cons _ x _ xbar)) H0) (interval_lb h) (interval_ub h)).
    }
Defined.

Lemma IIRInt_unfold_nil f r :
  IIRInt 0 f r = 0.
Proof. rewrite //=. Qed.

Lemma IIRInt_unfold_vsingle f i :
  IIRInt 1 f (vsingle i) = IRInt (λ x, f (vsingle x)) (interval_lb i) (interval_ub i).
Proof. rewrite //=. Qed.

Lemma IIRInt_unfold_cons n (f : Vector.t R (S (S n)) -> R) i r:
  IIRInt (S (S n)) f (cons _ i _ r) =
  IRInt (λ x, IIRInt (S n) (λ xbar, f (cons _ x _ xbar)) r) (interval_lb i) (interval_ub i).
Proof. rewrite //=. Qed.

Opaque IIRInt.

Inductive is_IIRInt : forall n, (Vector.t R n -> R) -> rectangle n -> R -> Prop :=
  | is_IIRint_1d (f: Vector.t R 1 -> R) (i: interval) (v : R) :
    is_IRInt (λ x, f (vsingle x)) (interval_lb i) (interval_ub i) v ->
    is_IIRInt 1 f (vsingle i) v
  | is_IIRint_cons n (f : Vector.t R (S (S n)) -> R) (i: interval) (r: rectangle (S n)) (v : R) :
    (∀ x, in_interval x i -> ∃ v', is_IIRInt (S n) (λ xbar, f (cons _ x _ xbar)) r v') ->
    is_IRInt (λ x, IIRInt (S n) (λ xbar, f (cons _ x _ xbar)) r) (interval_lb i) (interval_ub i) v ->
    is_IIRInt (S (S n)) f (cons _ i _ r) v.

Definition ex_IIRInt n f r :=
  ∃ v, is_IIRInt n f r v.

Lemma IIRInt_correct n f r :
  ex_IIRInt n f r -> is_IIRInt n f r (IIRInt n f r).
Proof.
  rewrite /ex_IIRInt. intros (v&His).
  destruct n.
  { inversion His. }

  induction n as [| n' IH]; inversion His; subst; sigT_inj.
  - rewrite IIRInt_unfold_vsingle. econstructor.
    apply IRInt_correct. eexists; eauto.
  - rewrite IIRInt_unfold_cons. econstructor; eauto.
    apply IRInt_correct. eexists; eauto.
Qed.

Lemma is_IIRInt_unique n f r v :
  is_IIRInt n f r v -> IIRInt n f r = v.
Proof.
  intros His.
  destruct n.
  { inversion His. }

  induction n as [| n' IH]; inversion His; subst; sigT_inj.
  - rewrite IIRInt_unfold_vsingle. apply is_IRInt_unique; auto.
  - rewrite IIRInt_unfold_cons. apply is_IRInt_unique; auto.
Qed.

Lemma is_IIRInt_ext:
  ∀ n f g r (v : R),
    wf_rectangle n r →
    (∀ x, in_rectangle x r → f x = g x) →
    is_IIRInt n f r v → is_IIRInt n g r v.
Proof.
  intros n.
  destruct n.
  { intros ???? Hwf Hext His. inversion His. }

  induction n as [| n' IH] => f g r v Hwf Hext His; inversion His; subst; sigT_inj.
  - econstructor. eapply is_IRInt_ext; eauto.
    { inversion Hwf; sigT_inj; eauto. }
    { intros. apply Hext. rewrite /in_rectangle.
      apply Forall2_cons; last apply Forall2_nil.
      split; intuition.
    }
  - econstructor.
    { intros. edestruct H2 as (v'&Hv'); eauto. exists v'. eapply IH; eauto.
      { inversion Hwf; sigT_inj; eauto. }
      intros. eapply Hext. econstructor; eauto.
    }
    eapply is_IRInt_ext.
    { inversion Hwf; sigT_inj; eauto. }
    { intros. symmetry. apply is_IIRInt_unique.
      eapply IH.
      { inversion Hwf; sigT_inj; eauto. }
      { intros. eapply Hext. econstructor; eauto. }
      eapply IIRInt_correct. edestruct (H2 x); eauto.
      eexists; eauto.
    }
    eauto.
Qed.

Ltac nil_vect :=
  repeat  match goal with
    | [ H : t ?A 0 |- _ ] =>
      assert (H = @nil _) by (dependent induction H; auto); subst
  end.


Lemma IIRInt_ext n f g r :
  wf_rectangle n r →
  (∀ x, in_rectangle x r → f x = g x) ->
  IIRInt n f r = IIRInt n g r.
Proof.
  revert f g r.
  destruct n.
  { intros ??? Hwf Hext. rewrite ?IIRInt_nil //. }

  induction n as [| n' IH] => f g r Hwf Hext.
  - inversion Hwf. sigT_inj; nil_vect.
    rewrite (IIRInt_unfold_vsingle).
    rewrite (IIRInt_unfold_vsingle).
    eapply IRInt_ext; eauto.
    { intros y Hlt. apply Hext. econstructor; eauto. econstructor. }
  - inversion Hwf; sigT_inj.
    rewrite IIRInt_unfold_cons.
    rewrite IIRInt_unfold_cons.
    eapply IRInt_ext; auto.
    intros y Hlt. eapply IH; eauto.
    intros. apply Hext. econstructor; eauto.
Qed.

Lemma is_IIRInt_scal:
  ∀ n f r k (v : R),
    wf_rectangle n r →
    is_IIRInt n f r v → is_IIRInt n (λ y, scal k (f y)) r (scal k v).
Proof.
  intros n f r k v Hwf His.
  destruct n.
  { inversion His. }

  revert v His.
  induction n as [| n' IH] => v His; inversion His; subst; sigT_inj.
  - econstructor. eapply is_IRInt_scal; auto.
    rewrite /wf_rectangle in Hwf. inversion Hwf; subst; sigT_inj; eauto.
  - econstructor.
    { intros y Hin. edestruct (H2 y) as (v'&Hv'); eauto. eexists.
      eapply IH; eauto.
      { inversion Hwf; sigT_inj; eauto. }
    }
    eapply (is_IRInt_ext (λ x, scal k (IIRInt _ (λ xbar, f (cons R x (S n') xbar)) _))).
    { inversion Hwf; eauto. }
    { intros. symmetry. apply is_IIRInt_unique.
      eapply IH.
      { inversion Hwf; sigT_inj; eauto. }
      eapply IIRInt_correct. edestruct (H2 x); eauto.
      eexists; eauto.
    }
    eapply is_IRInt_scal; eauto.
    { inversion Hwf; eauto. }
Qed.

Lemma IIRInt_scal:
  ∀ n f r k,
    wf_rectangle n r →
    ex_IIRInt n f r →
    IIRInt n (λ y, scal k (f y)) r =
    scal k (IIRInt n f r).
Proof.
  intros n f r k Hwf Hex.
  apply is_IIRInt_unique, is_IIRInt_scal; auto.
  apply IIRInt_correct; auto.
Qed.

Definition strict_monotone_on_interval (i: interval) (f: R -> R) :=
  (∀ (x y : R), Rbar_lt (interval_lb i) x /\ x < y /\ Rbar_lt y (interval_ub i) ->
                f x < f y).

Inductive Forall3 {A B C : Type} (P : A → B → C → Prop) : ∀ n : nat, t A n → t B n → t C n → Prop :=
    Forall3_nil : Forall3 P _ (nil A) (nil B) (nil C)
  | Forall3_cons : ∀ (m : nat) (x1 : A) (x2 : B) (x3 :C) (v1 : t A m) (v2 : t B m) (v3: t C m),
                     P x1 x2 x3 → Forall3 P _ v1 v2 v3 →
                     Forall3 P _ (cons A x1 m v1) (cons B x2 m v2) (cons C x3 m v3).

Arguments Forall3 {A B C}%type_scope _%function_scope {n}%nat_scope.
Arguments Forall3_nil {A B C}%type_scope _%function_scope.
Arguments Forall3_cons {A B C}%type_scope _%function_scope {m}%nat_scope.

Definition continuous_derive_on_interval (i: interval) (g: R -> R) (dg: R -> R) :=
  (∀ (x : R), Rbar_lt (interval_lb i) x /\ Rbar_lt x (interval_ub i) →
              is_derive g x (dg x) ∧ continuous dg x).

Definition is_interval_image (g: R -> R) (i i': interval) :=
  (∀ (x : R), Rbar_lt (interval_lb i) x /\ Rbar_lt x (interval_ub i) →
              Rbar_lt (interval_lb i') (g x) /\ Rbar_lt (g x) (interval_ub i')) /\
  is_right_lim g (interval_lb i) (interval_lb i') /\
  is_left_lim g (interval_ub i) (interval_ub i').

Definition vector_apply {A B n} (fs: Vector.t (A -> B) n) (xs: Vector.t A n) : Vector.t B n :=
  VectorDef.map2 (λ f x, f x) fs xs.

Definition vector_mult {n} (xs: Vector.t R n) : R :=
  VectorDef.fold_right (Rmult) xs 1.

Lemma is_interval_image_spec f i1 i2 x:
    is_interval_image f i1 i2 →
    in_interval x i1 →
    in_interval (f x) i2.
Proof.
  intros (Hrange&_). apply Hrange.
Qed.

Lemma is_IIRInt_comp_noncont n (f : Vector.t R n → R)
      (gs dgs : Vector.t (R → R) n) (r r': rectangle n) :
  wf_rectangle n r  ->
  Forall2 strict_monotone_on_interval r gs ->
  Forall3 is_interval_image gs r r' ->
  Forall3 continuous_derive_on_interval r gs dgs ->
  ex_IIRInt n f r' ->
  is_IIRInt n (fun y => vector_mult (vector_apply dgs y) * (f (vector_apply gs y))) r (IIRInt n f r').
Proof.
  revert r r' f gs dgs.
  destruct n as [| n].
  { intros r r' f gs dgs Hwf Hmono Himage Hderive Hex. destruct Hex as (?&His). inversion His. }

  induction n as [| n' IH].
  - intros r r' f gs dgs Hwf Hmono Himage Hderive Hex.
    inversion Hwf; sigT_inj; eauto.
    inversion Himage. subst; sigT_inj.
    nil_vect. econstructor.
    dependent destruction dgs; nil_vect.
    simpl. rewrite /vector_mult. simpl.
    inversion Hderive; subst. sigT_inj.
    rewrite IIRInt_unfold_vsingle.
    eapply is_IRInt_ext; last first.
    { eapply is_IRInt_comp_noncont_strict; eauto; try eapply H6.
      { inversion Hmono; sigT_inj; eauto. }
      destruct Hex as (?&His). inversion His; sigT_inj. eexists; eauto. }
    { intros. simpl. rewrite /vsingle/scal//=/mult/=. nra. }
    { eauto. }
  - intros r r' f gs dgs Hwf Hmono Himage Hderive Hex.
    inversion Hwf; sigT_inj; eauto.
    inversion Himage. subst; sigT_inj.
    econstructor.
    { intros. destruct Hex as (v'&His).
      inversion His; sigT_inj.
      assert (Hin: in_interval (x1 x0) x3).
      {
        eapply is_interval_image_spec; eauto.
      }
      edestruct (H8 _ Hin) as (vsub&Hvsub).
      inversion Hderive; sigT_inj.
      eexists.
      simpl.
      rewrite /vector_mult /=.
      eapply is_IIRInt_ext; first eauto.
      { intros. rewrite Rmult_assoc. reflexivity. }
      eapply (is_IIRInt_scal (S n')); eauto.
      { eapply (IH _ _ (λ y, f (cons _ (x1 x0) _ y))); eauto.
        { inversion Hmono; sigT_inj; eauto. }
        { eexists; eauto. }
      }
    }
    inversion Hderive; sigT_inj.
    simpl.
    eapply (is_IRInt_ext (λ x, (scal (x4 x) (IIRInt _ (λ xbar, f (cons _ (x1 x) _ xbar)) _)))); first eauto.
    { intros. simpl.
      inversion Hderive; sigT_inj.
      rewrite /vector_mult /=.
      symmetry.
      erewrite IIRInt_ext; last first.
      { intros. rewrite Rmult_assoc. reflexivity. }
      { eauto. }
      rewrite IIRInt_scal; eauto.
      {
        f_equal.
        apply is_IIRInt_unique.
        assert (Hin: in_interval (x1 x0) x3).
        {
          eapply is_interval_image_spec; eauto.
        }
        eapply (IH _ _ (λ y, f (cons _ (x1 x0) _ y))); eauto.
        { inversion Hmono; sigT_inj; eauto. }
        { destruct Hex as (?&His).
          inversion His; subst; sigT_inj.
          { edestruct H11; eauto. eexists; eauto. }
        }
      }
      {
        assert (Hin: in_interval (x1 x0) x3).
        {
          eapply is_interval_image_spec; eauto.
        }
        destruct Hex as (?&His).
        inversion His; subst; sigT_inj.
        eexists.
        eapply (IH _ _ (λ y, f (cons _ (x1 x0) _ y))); eauto.
        { inversion Hmono; sigT_inj; eauto. }
        { edestruct H11; eauto. eexists; eauto. }
      }
    }
    rewrite IIRInt_unfold_cons.
    eapply (is_IRInt_comp_noncont_strict (λ x0, IIRInt (S n') (λ y, f (cons _ x0 _ y)) v3)); eauto.
    { inversion Hmono; eauto. }
    { inversion Himage; eauto; sigT_inj; eapply H8. }
    { inversion Himage; eauto; sigT_inj; eapply H8. }
    { inversion Himage; eauto; sigT_inj; eapply H8. }
    destruct Hex as (?&His). inversion His; sigT_inj. eexists; eauto.
Qed.

Section marginal.

Variable (V: Type).

Definition is_marginalized_to (f : V -> R -> R) (int: interval) (g: V -> R) :=
  (∀ v, is_IRInt (f v) (interval_lb int) (interval_ub int) (g v)).

Definition Marginal f int (v : V) :=
  IRInt (f v) (interval_lb int) (interval_ub int).

End marginal.
