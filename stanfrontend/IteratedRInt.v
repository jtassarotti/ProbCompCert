Require Import Utf8.

Inductive Forall3 {A B C : Type} (P : A → B → C → Prop) : list A → list B → list C → Prop :=
    Forall3_nil : Forall3 P (nil) (nil) (nil)
  | Forall3_cons : ∀ (x1 : A) (x2 : B) (x3 :C) (v1 : list A) (v2 : list B) (v3: list C),
                     P x1 x2 x3 → Forall3 P v1 v2 v3 →
                     Forall3 P (cons x1 v1) (cons x2 v2) (cons x3 v3).

Arguments Forall3 {A B C}%type_scope _%function_scope.
Arguments Forall3_nil {A B C}%type_scope _%function_scope.
Arguments Forall3_cons {A B C}%type_scope _%function_scope.



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
Definition rectangle_subset {n} (r1 r2: rectangle n) :=
  Forall2 interval_subset r1 r2.

Definition wf_interval (i: interval) :=
  Rbar_lt (interval_lb i) (interval_ub i).
Definition wf_rectangle (n: nat) (v: rectangle n) :=
  VectorDef.Forall wf_interval v.
Definition wf_rectangle_list (v: list interval) :=
  List.Forall wf_interval v.

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

Inductive VectorForall3 {A B C : Type} (P : A → B → C → Prop) : ∀ n : nat, t A n → t B n → t C n → Prop :=
    VectorForall3_nil : VectorForall3 P _ (nil A) (nil B) (nil C)
  | VectorForall3_cons : ∀ (m : nat) (x1 : A) (x2 : B) (x3 :C) (v1 : t A m) (v2 : t B m) (v3: t C m),
                     P x1 x2 x3 → VectorForall3 P _ v1 v2 v3 →
                     VectorForall3 P _ (cons A x1 m v1) (cons B x2 m v2) (cons C x3 m v3).

Arguments VectorForall3 {A B C}%type_scope _%function_scope {n}%nat_scope.
Arguments VectorForall3_nil {A B C}%type_scope _%function_scope.
Arguments VectorForall3_cons {A B C}%type_scope _%function_scope {m}%nat_scope.

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
  VectorForall3 is_interval_image gs r r' ->
  VectorForall3 continuous_derive_on_interval r gs dgs ->
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

(* The same theory as IIRInt using lists instead of vectors *)

Import List.

Section IIRInt_list.
Definition rectangle_list := list (interval).
Definition in_list_rectangle (x: list R) (r: rectangle_list) :=
  List.Forall2 in_interval x r.
Definition rectangle_list_subset (r1 r2: rectangle_list) :=
  List.Forall2 interval_subset r1 r2.

Lemma in_list_rectangle_wf_rectangle p l :
  in_list_rectangle p l ->
  wf_rectangle_list l.
Proof.
  induction 1.
  - econstructor.
  - econstructor; eauto.
    destruct H. eapply Rbar_lt_trans; eauto.
Qed.

Fixpoint IIRInt_list (f: list R -> R) (r: rectangle_list) : R :=
  match r with
  | nil => 0
  | i :: nil =>
      IRInt (λ x, f (x :: nil)) (interval_lb i) (interval_ub i)
  | i :: r' =>
      IRInt (λ x, IIRInt_list (λ xbar, f (x :: xbar)) r') (interval_lb i) (interval_ub i)
  end.

Lemma IIRInt_list_unfold_nil f :
  IIRInt_list f nil = 0.
Proof. rewrite //=. Qed.

Lemma IIRInt_list_unfold_single f i :
  IIRInt_list f (i :: nil) = IRInt (λ x, f (x :: nil)) (interval_lb i) (interval_ub i).
Proof. rewrite //=. Qed.

Lemma IIRInt_list_unfold_cons f i r:
  r <> nil ->
  IIRInt_list f (i :: r) =
  IRInt (λ x, IIRInt_list (λ xbar, f (x :: xbar)) r) (interval_lb i) (interval_ub i).
Proof.
  intros Hneq.
  destruct r; first try congruence.
  auto.
Qed.

Inductive is_IIRInt_list : (list R -> R) -> rectangle_list -> R -> Prop :=
  | is_IIRint_list_1d (f: list R -> R) (i: interval) (v : R) :
    is_IRInt (λ x, f (x :: nil)) (interval_lb i) (interval_ub i) v ->
    is_IIRInt_list f (i :: nil) v
  | is_IIRint_list_cons (f : list R -> R) (i: interval) (r: rectangle_list) (v : R) :
    r <> nil ->
    (∀ x, in_interval x i -> ∃ v', is_IIRInt_list (λ xbar, f (x :: xbar)) r v') ->
    is_IRInt (λ x, IIRInt_list (λ xbar, f (x :: xbar)) r) (interval_lb i) (interval_ub i) v ->
    is_IIRInt_list f (i :: r) v.

Definition ex_IIRInt_list f r :=
  ∃ v, is_IIRInt_list f r v.

Lemma IIRInt_list_correct f r :
  ex_IIRInt_list f r -> is_IIRInt_list f r (IIRInt_list f r).
Proof.
  rewrite /ex_IIRInt. intros (v&His).
  induction His.
  - econstructor; rewrite IIRInt_list_unfold_single. apply IRInt_correct. eexists; eauto.
  - econstructor; eauto. rewrite IIRInt_list_unfold_cons; eauto.
    apply IRInt_correct. eexists; eauto.
Qed.

Lemma is_IIRInt_list_unique f r v :
  is_IIRInt_list f r v -> IIRInt_list f r = v.
Proof.
  intros His.
  induction His.
  - rewrite IIRInt_list_unfold_single. apply is_IRInt_unique; auto.
  - rewrite IIRInt_list_unfold_cons; auto. apply is_IRInt_unique; auto.
Qed.

Lemma IIRInt_list_IIRInt1 f r :
  wf_rectangle _ (Vector.of_list r) ->
  IIRInt_list f r =
  IIRInt _ (λ x, f (Vector.to_list x)) (Vector.of_list r).
Proof.
  revert f.
  induction r; intros f Hwf.
  - rewrite //=.
  - destruct r.
    * rewrite //=.
    * rewrite IIRInt_unfold_cons. rewrite IIRInt_list_unfold_cons; last done. eapply IRInt_ext.
      { inversion Hwf. subst. sigT_inj. eauto. }
      intros x Hlt. 
      rewrite IHr; last first.
      { inversion Hwf. subst. sigT_inj. eauto. }
      simpl.
      eapply IIRInt_ext.
      { inversion Hwf; subst. sigT_inj; eauto. }
      intros. rewrite //=.
Qed.

Lemma IIRInt_list_ext f g r :
  wf_rectangle_list r →
  (∀ x, in_list_rectangle x r → f x = g x) ->
  IIRInt_list f r = IIRInt_list g r.
Proof.
  revert f g.
  destruct r as [| i1 r].
  { rewrite //=. }
  revert i1.
  induction r as [| i2 r' IH] => i1 f g Hwf Hext.
  - inversion Hwf; sigT_inj; nil_vect.
    rewrite (IIRInt_list_unfold_single).
    rewrite (IIRInt_list_unfold_single).
    eapply IRInt_ext; eauto.
    { intros y Hlt. apply Hext. econstructor; eauto. }
  - inversion Hwf; sigT_inj.
    rewrite IIRInt_list_unfold_cons; last done.
    rewrite IIRInt_list_unfold_cons; last done.
    eapply IRInt_ext; auto.
    intros y Hlt. eapply IH; eauto.
    intros. apply Hext. econstructor; eauto.
Qed.


Lemma is_IIRInt_list_ext:
  ∀ f g r (v : R),
    wf_rectangle_list r →
    (∀ x, in_list_rectangle x r → f x = g x) →
    is_IIRInt_list f r v → is_IIRInt_list g r v.
Proof.
  intros f g r.
  revert f g.
  destruct r as [| i1 r]; intros f g v Hwf Hext His.
  { inversion His. }
  revert i1 v f g Hwf Hext His.
  induction r as [| i2 r' IH] => i1 v f g Hwf Hext His.
  - inversion His; subst; last by congruence.
    econstructor.
    eapply is_IRInt_ext; eauto.
    { inversion Hwf; eauto. }
    intros. eapply Hext. econstructor; eauto.
  - inversion His; subst.
    econstructor; first congruence.
    { intros. edestruct H3; eauto. eexists. eapply IH; eauto.
      { inversion Hwf; eauto. }
      { intros. eapply Hext. econstructor; eauto. }
    }
    eapply is_IRInt_ext; eauto.
    { inversion Hwf; eauto. }
    { intros. eapply IIRInt_list_ext; eauto.
      { inversion Hwf; eauto. }
      intros. eapply Hext. econstructor; eauto.
    }
Qed.

Lemma is_IIRInt_list_scal:
  ∀ f r k (v : R),
    wf_rectangle_list r →
    is_IIRInt_list f r v → is_IIRInt_list (λ y, scal k (f y)) r (scal k v).
Proof.
  intros f r k v Hwf His.
  destruct r as [| i1 r].
  { inversion His. }

  revert i1 f v Hwf His.
  induction r as [| i2 r' IH] => i1 f v Hwf His; inversion His; subst; try congruence.
  - econstructor. eapply is_IRInt_scal; auto.
    inversion Hwf; subst; sigT_inj; eauto.
  - econstructor; eauto.
    { intros y Hin. edestruct (H3 y) as (v'&Hv'); eauto. eexists.
      eapply IH; eauto.
      { inversion Hwf; sigT_inj; eauto. }
    }
    eapply (is_IRInt_ext (λ x, scal k (IIRInt_list (λ xbar, f (x :: xbar)) _))).
    { inversion Hwf; eauto. }
    { intros. symmetry. apply is_IIRInt_list_unique.
      eapply IH.
      { inversion Hwf; sigT_inj; eauto. }
      eapply IIRInt_list_correct. edestruct (H3 x); eauto.
      eexists; eauto.
    }
    eapply is_IRInt_scal; eauto.
    { inversion Hwf; eauto. }
Qed.

Lemma IIRInt_list_scal:
  ∀ f r k,
    wf_rectangle_list r →
    ex_IIRInt_list f r →
    IIRInt_list (λ y, scal k (f y)) r =
    scal k (IIRInt_list f r).
Proof.
  intros f r k Hwf Hex.
  apply is_IIRInt_list_unique, is_IIRInt_list_scal; auto.
  apply IIRInt_list_correct; auto.
Qed.

Definition list_apply {A B} (fs: list (A -> B)) (xs: list A) : list B :=
  List.map (λ fx, (fst fx) (snd fx)) (List.combine fs xs).

Definition list_plus (xs: list R) : R :=
  List.fold_right (Rplus) 0 xs.

Definition list_mult (xs: list R) : R :=
  List.fold_right (Rmult) 1 xs.

Lemma is_IIRInt_list_comp_noncont (f : list R → R)
      (gs dgs : list (R → R)) (r r': rectangle_list) :
  wf_rectangle_list r  ->
  List.Forall2 strict_monotone_on_interval r gs ->
  Forall3 is_interval_image gs r r' ->
  Forall3 continuous_derive_on_interval r gs dgs ->
  ex_IIRInt_list f r' ->
  is_IIRInt_list (fun y => list_mult (list_apply dgs y) * (f (list_apply gs y))) r (IIRInt_list f r').
Proof.
  revert r' f gs dgs.
  destruct r as [| i1 r].
  { intros r' f gs dgs Hwf Hmono Himage Hderive Hex. destruct Hex as (?&His).
    assert (r' = nil).
    { inversion Himage. eauto. }
    { subst. inversion His. }
  }

  revert i1.
  induction r as [|i2 r IH].
  - intros i1 r' f gs dgs Hwf Hmono Himage Hderive Hex.
    inversion Hwf; sigT_inj; eauto.
    inversion Himage. subst; sigT_inj.
    econstructor.
    dependent destruction dgs; nil_vect.
    { inversion Hderive. }
    simpl. rewrite /list_mult. simpl.
    inversion Hderive; subst. sigT_inj.
    inversion H10. subst. simpl.
    inversion H8. subst.
    eapply is_IRInt_ext; last first.
    { eapply is_IRInt_comp_noncont_strict; eauto; try eapply H6.
      { inversion Hmono; sigT_inj; eauto. }
      destruct Hex as (?&His). inversion His; sigT_inj; subst.
      { eexists; eauto. }
      congruence.
    }
    { intros. simpl. rewrite /vsingle/scal//=/mult/=. rewrite /list_apply//=. nra. }
    { eauto. }
  - intros i1 r' f gs dgs Hwf Hmono Himage Hderive Hex.
    inversion Hwf; sigT_inj; eauto.
    inversion Himage. subst; sigT_inj.
    rewrite IIRInt_list_unfold_cons; last first.
    { inversion H8. subst. congruence. }
    econstructor; eauto.
    { congruence. }
    { intros. destruct Hex as (v'&His); eauto.
      inversion H8; subst.
      inversion His; sigT_inj; subst.
      assert (Hin: in_interval (x1 x) x3).
      {
        eapply is_interval_image_spec; eauto.
      }
      edestruct (H10 _ Hin) as (vsub&Hvsub).
      inversion Hderive; sigT_inj.
      eexists.
      simpl.
      rewrite /vector_mult /=.
      eapply is_IIRInt_list_ext; first eauto.
      { intros. rewrite Rmult_assoc. reflexivity. }
      eapply (is_IIRInt_list_scal ); eauto.
      { eapply (IH _ _ (λ y, f (cons (x1 x) y))); eauto.
        { inversion Hmono; sigT_inj; eauto. }
        { eexists; eauto. }
      }
    }
    inversion Hderive; sigT_inj. subst.
    eapply (is_IRInt_ext (λ x, (scal (x4 x) (IIRInt_list (λ xbar, f (cons (x1 x) xbar)) _)))); first eauto.
    {
      intros.
      symmetry.
      transitivity
        (scal (x4 x)
           (IIRInt_list (λ xbar, list_mult (list_apply v4 xbar) * f (list_apply (x1 :: v1) (x :: xbar))) (i2 :: r))).
      { 
        rewrite -IIRInt_list_scal; eauto.
        { eapply IIRInt_list_ext; eauto.
          intros. rewrite //=. rewrite Rmult_assoc. reflexivity. }
        { eexists.
          eapply (IH _ _ (λ y, f (cons (x1 x)  y))); eauto.
          { inversion Hmono; sigT_inj; eauto. }
          { destruct Hex as (?&His).
            assert (Hin: in_interval (x1 x) x3).
            {
              eapply is_interval_image_spec; eauto.
            }
            inversion H8. subst.
            inversion His; subst; sigT_inj.
            edestruct H12; eauto. eexists; eauto.
          }
        }
      }
      f_equal.
      eapply is_IIRInt_list_unique.
      assert (Hin: in_interval (x1 x) x3).
      {
        eapply is_interval_image_spec; eauto.
      }
      eapply (IH _ _ (λ y, f (cons (x1 x) y))); eauto.
      { inversion Hmono; sigT_inj; eauto. }
      { destruct Hex as (?&His).
        inversion H8. subst.
        inversion His; subst; sigT_inj.
        { edestruct H12; eauto. eexists; eauto. }
      }
    }
    inversion H8. subst.
    eapply (is_IRInt_comp_noncont_strict (λ x0, IIRInt_list (λ y, f (cons x0 y)) (x5 :: v5))); eauto.
    { inversion Hmono; eauto. }
    { inversion Himage; eauto; sigT_inj; eapply H6. }
    { inversion Himage; eauto; sigT_inj; eapply H6. }
    { inversion Himage; eauto; sigT_inj; eapply H6. }
    destruct Hex as (?&His). inversion His; sigT_inj. eexists; eauto.
Qed.
End IIRInt_list.
