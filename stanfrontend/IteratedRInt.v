From Coq Require Import Reals Psatz ssreflect ssrbool Utf8 Vector.
From mathcomp Require Import eqtype seq.

From Coquelicot Require Import Markov Rcomplements Lub Lim_seq SF_seq Continuity Hierarchy RInt RInt_analysis Derive.
From Coquelicot Require Export Rbar.

Require Import RealsExt ImproperRInt.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Record interval := mk_interval { interval_lb : Rbar; interval_ub : Rbar}.

Definition interval_subset (i1 i2: interval) :=
  Rbar_le (interval_lb i2) (interval_lb i1) /\ Rbar_le (interval_ub i1) (interval_ub i2).

Definition rectangle n := Vector.t (interval) n.
Definition vsingle {A: Type} (a: A) :=
  cons A a O (nil A).
Definition in_interval (x: R) (i: interval) :=
  Rbar_le (interval_lb i) x /\ Rbar_le x (interval_ub i).

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

  induction n as [| n' IH].
  - inversion His; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H0; subst.
    rewrite IIRInt_unfold_vsingle. econstructor.
    apply IRInt_correct. eexists; eauto.
  - inversion His; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H0; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H1; subst.
    rewrite IIRInt_unfold_cons. econstructor; eauto.
    apply IRInt_correct. eexists; eauto.
Qed.

Lemma is_IIRInt_unique n f r v :
  is_IIRInt n f r v -> IIRInt n f r = v.
Proof.
  intros His.
  destruct n.
  { inversion His. }

  induction n as [| n' IH].
  - inversion His; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H0; subst.
    rewrite IIRInt_unfold_vsingle. apply is_IRInt_unique; auto.
  - inversion His; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H0; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H1; subst.
    rewrite IIRInt_unfold_cons. apply is_IRInt_unique; auto.
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
  induction n as [| n' IH] => v His.
  - inversion His; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H0; subst.
    econstructor. eapply is_IRInt_scal; auto.
    rewrite /wf_rectangle in Hwf. inversion Hwf. subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H2; subst.
    eauto.
  - inversion His; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H0; subst.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H1; subst.
    econstructor.
    { intros y Hin. edestruct (H2 y) as (v'&Hv'); eauto. eexists.
      eapply IH; eauto.
      { inversion Hwf; eauto; subst. eauto.
        apply Classical_Prop.EqdepTheory.inj_pair2 in H1; subst.
        eauto.
      }
    }
    eapply (is_IRInt_ext (λ x, scal k (IIRInt _ (λ xbar, f (cons R x (S n') xbar)) _))).
    { inversion Hwf; eauto. }
    { intros. symmetry. apply is_IIRInt_unique.
      eapply IH.
      { inversion Hwf; eauto; subst. eauto.
        apply Classical_Prop.EqdepTheory.inj_pair2 in H4; subst.
        eauto.
      }
      eapply IIRInt_correct. edestruct (H2 x); eauto.
      { split; apply Rbar_lt_le; intuition. }
      eexists; eauto.
    }
    eapply is_IRInt_scal; eauto.
    { inversion Hwf; eauto. }
Qed.

Section marginal.

Variable (V: Type).

Definition is_marginalized_to (f : V -> R -> R) (int: interval) (g: V -> R) :=
  (∀ v, is_IRInt (f v) (interval_lb int) (interval_ub int) (g v)).

Definition Marginal f int (v : V) :=
  IRInt (f v) (interval_lb int) (interval_ub int).

End marginal.
