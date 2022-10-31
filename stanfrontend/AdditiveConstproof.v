From Coq Require Import Reals Psatz ssreflect Utf8.
Require Import Smallstep.
Require Import Errors.
Require Import Linking.
Require Import Globalenvs.

Require Import Maps.
Require Import Stanlight.
Require Import Ssemantics.
Require Import AdditiveConst.
Require Import DenotationalSimulationAdditive.
Require Import Coqlib.
Require Import Transforms.
Require Import IteratedRInt.
Require Import Memory.
Require Import ParamMap.
Require Import StanEnv.

Require Import Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => None end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => None end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : option_monad_scope.

Local Open Scope option_monad_scope.

Definition math_fun_const : PTree.t R :=
   PTree.set ($"normal_lpdf") (ln(1/sqrt(2 * PI)))
  (PTree.set ($"cauchy_lpdf") (ln(1/PI)) (PTree.empty _)).


Definition match_prog (p: program) (tp: program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp /\
  pr_data_vars p = pr_data_vars tp /\
  pr_parameters_vars p = pr_parameters_vars tp.

(* Returns the constant dropped by switching from the indicated function
   to its "u" variant *)

Fixpoint compute_const_expr (e: Stanlight.expr) {struct e} : R :=
  match e with
  | Econst_float f Breal => IFR f
  | Ecall (Evar id (Bfunction _ _)) el ty =>
      match PTree.get id math_fun_const with
      | Some r => r
      | None => 0
      end
  | Ebinop e1 Stanlight.Plus e2 Breal =>
      match typeof e1, typeof e2 with
      | Breal, Breal => (compute_const_expr e1) + (compute_const_expr e2)
      | _, _ => 0
      end
  | Ebinop e1 Minus e2 Breal =>
      match typeof e1, typeof e2 with
      | Breal, Breal => (compute_const_expr e1) - (compute_const_expr e2)
      | _, _ => 0
      end
  | _ => 0
  end.

Local Open Scope R.
Fixpoint compute_const_statement' (s: Stanlight.statement) {struct s} : option R :=
  match s with
  | Sskip => Some 0
  | Sassign e1 o e2 => Some 0
  | Ssequence s1 s2 =>
    do s1 <- (compute_const_statement' s1);
    do s2 <- (compute_const_statement' s2);
    Some (s1 + s2)
  | Sifthenelse e s1 s2 =>
    Some 0
  | Sfor i (Econst_int i1 Bint) (Econst_int i2 Bint) s =>
    match check_no_assign i s with
    | true =>
        do r <- compute_const_statement' s;
        let i1' := Integers.Int.unsigned i1 in
        let i2' := Integers.Int.unsigned i2 in
        Some (r * IZR (Z.max (i2' - i1' + 1)%Z 0)%Z)
    | false =>
        Some 0
    end
  | Sfor i e1 e2 s =>
    Some 0
  | Starget e => Some (compute_const_expr e)
  | Stilde e d el => None
  end.

Definition compute_const_statement s :=
  match compute_const_statement' s with
  | Some r => r
  | None => 0
  end.

Lemma transf_program_match:
  forall p: program,  match_prog p (transf_program p).
Proof.
  intros. unfold match_prog.
  unfold transf_program. destruct p; simpl.
  repeat split; eauto.
  eapply match_transform_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Variable data : list Values.val.
Variable params : list Values.val.
Variable TRANSL: match_prog prog tprog.
Let ge := globalenv prog.
Let tge := globalenv tprog.

Hint Unfold match_prog : core.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  intros. destruct TRANSL as (Hmatch&?).
  eapply Genv.find_funct_transf in Hmatch; eauto.
Qed.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof.
  intros. destruct TRANSL as (Hmatch&?).
  eapply Genv.find_funct_ptr_transf in Hmatch; eauto.
Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. destruct TRANSL as (Hmatch&?).
  eapply Genv.find_symbol_transf; eauto.
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  intros. destruct TRANSL.
  eapply Genv.senv_transf; eauto.
Qed.

Lemma external_funct_preserved:
  match_external_funct (globalenv prog) (globalenv tprog).
Proof.
  destruct TRANSL as (Hmatch&_). eapply match_program_external_funct; eauto.
  intros. simpl. congruence.
Qed.

Remark some_bind_inversion:
  forall (A B: Type) (f: option A) (g: A -> option B)
         (y: B),
  (do x <- f; g x) = Some y ->
  exists x : A,
  f = Some x /\ g x = Some y.
Proof. intros A B f g y. destruct f => //=. eauto. Qed.

Remark none_bind_inversion:
  forall (A B: Type) (f: option A) (g: A -> option B),
  (do x <- f; g x) = None ->
  f = None ∨ (∃ x, f= Some x /\ g x = None).
Proof. intros A B f g Heq. destruct f => //=; eauto. Qed.

Ltac monadInv1 H :=
  match type of H with
  | (Some _ = Some _) =>
      inversion H; clear H; try subst
  | (None = Some _) =>
      discriminate
  | ((do _ <- ?F; ?G _) = Some ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
       destruct (some_bind_inversion _ _ _ _ _ H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInv1 EQ2))))
  | (match ?X with left _ => _ | right _ => assertion_failed end = OK _) =>
      destruct X; [try (monadInv1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; simpl negb in H; [discriminate | try (monadInv1 H)]
  | (match ?X with true => _ | false => assertion_failed end = OK _) =>
      destruct X as [] eqn:?; [try (monadInv1 H) | discriminate]
  | (mmap ?F ?L = OK ?M) =>
      generalize (mmap_inversion F L H); intro
  end.

Ltac monadInv H :=
  monadInv1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = Some _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

Ltac checkInv :=
  repeat match goal with
    | [ H : check_no_target_expr _ = Some _ |- _] => monadInv H
    | [ H : check_no_target_exprlist _ = Some _ |- _] => monadInv H
    | [ H : unit |- _ ] => destruct H
  end.

Lemma evaluation_preserved_same en m pm t:
      (forall e v, eval_expr ge en m pm t e v ->
                   eval_expr tge en m pm t e v)
  /\  (forall el vl, eval_exprlist ge en m pm t el vl ->
                   eval_exprlist tge en m pm t el vl)
  /\  (forall e loc ofs, eval_llvalue ge en m pm t e loc ofs ->
                         eval_llvalue tge en m pm t e loc ofs)
  /\  (forall e loc ofs, eval_glvalue ge en m pm t e loc ofs ->
                         eval_glvalue tge en m pm t e loc ofs).
Proof.
  intros.
  apply (eval_exprs_ind ge en m pm t); intros; try (econstructor; eauto; done).
  - econstructor; eauto.
    { exploit (functions_translated); eauto. intros; subst. simpl; auto. }
    { eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved. }
  - intros. econstructor; eauto.
    rewrite symbols_preserved; auto.
Qed.

Lemma evaluation_preserved_no_target en m pm t t':
      (forall e v, eval_expr ge en m pm t e v ->
                   check_no_target_expr e = Some tt ->
                   eval_expr tge en m pm t' e v)
  /\  (forall el vl, eval_exprlist ge en m pm t el vl ->
                   check_no_target_exprlist el = Some tt ->
                   eval_exprlist tge en m pm t' el vl)
  /\  (forall e loc ofs, eval_llvalue ge en m pm t e loc ofs ->
                         check_no_target_expr e = Some tt ->
                         eval_llvalue tge en m pm t' e loc ofs)
  /\  (forall e loc ofs, eval_glvalue ge en m pm t e loc ofs ->
                         check_no_target_expr e = Some tt ->
                         eval_glvalue tge en m pm t' e loc ofs).
Proof.
  intros.
  apply (eval_exprs_ind ge en m pm t); intros; checkInv.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    { exploit (functions_translated); eauto. intros; subst. simpl; auto. }
    { eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved. }
  - econstructor; eauto.
  - econstructor; eauto.
  - intros. eapply eval_Eplvalue; eauto.
  - intros. eapply eval_Eglvalue; eauto.
  - econstructor.
  - intros. econstructor; eauto.
  - intros. econstructor.
  - intros. econstructor. eauto.
  - intros. econstructor; eauto.
    rewrite symbols_preserved; auto.
  - intros. econstructor; eauto.
Qed.

Lemma typeof_drop_const a :
  typeof (drop_const a) = typeof a.
Proof.
  induction a => //=.
  destruct b; eauto.
  destruct a; eauto;
  try destruct b0; eauto.
  { destruct (math_fun_remap ! i); eauto. }
  destruct b, b0 => //=.
  { destruct (typeof a1), (typeof a2) => //=. }
  { destruct (typeof a1), (typeof a2) => //=. }
Qed.

Lemma math_fun_remap_const i :
  (i = $"normal_lpdf" /\ math_fun_remap ! i = Some $"normal_lupdf"
   /\ math_fun_const ! i = Some (ln(1/sqrt(2 * PI)))) \/
  (i = $"cauchy_lpdf" /\ math_fun_remap ! i = Some $"cauchy_lupdf"
   /\ math_fun_const ! i = Some (ln(1/PI))) \/
  (math_fun_remap ! i = None /\ math_fun_const ! i = None).
Proof.
  rewrite /math_fun_const/math_fun_remap.
  destruct (Pos.eq_dec i $"normal_lpdf").
  { subst. rewrite ?PTree.gss; auto. }
  right.
  rewrite PTree.gso; last congruence.
  rewrite (@PTree.gso _ i $"normal_lpdf"); last congruence.
  destruct (Pos.eq_dec i $"cauchy_lpdf").
  { subst. rewrite ?PTree.gss; auto. }
  rewrite PTree.gso; last congruence.
  rewrite (@PTree.gso _ i $"cauchy_lpdf"); last congruence.
  rewrite ?PTree.gempty; auto.
Qed.

Lemma tprog_genv_has_mathlib :
  genv_has_mathlib (globalenv prog) ->
  genv_has_mathlib (globalenv tprog).
Proof.
  apply tprog_genv_has_mathlib; eauto using symbols_preserved, external_funct_preserved.
Qed.

Lemma evaluation_drop_const_aux en m pm t t' (MATH: genv_has_mathlib ge):
  no_shadow_pdflib en ->
  no_shadow_pdflib pm ->
      forall e v, eval_expr ge en m pm t e v ->
                   check_no_target_expr e = Some tt ->
                   ((drop_const e = e /\ compute_const_expr e = 0) \/
                   (∃ v', eval_expr tge en m pm t' (drop_const e) v' /\
                         match v with
                         | Values.Vfloat f =>
                             ∃ f', v' = Values.Vfloat f' /\ f' = IRF (IFR f - compute_const_expr e)
                         | _ => v' = v
                         end)).
Proof.
  intros HNOSHADOW1 HNOSHADOW2.
  exploit tprog_genv_has_mathlib; auto. intros MATHT.
  intros e v Heval.
  induction Heval; intros; checkInv; simpl; eauto.
  - destruct ty; eauto; [].
    right. eexists; split; econstructor; eauto. split; eauto.  rewrite -IRF_0. f_equal; nra.
  - destruct op; try eauto; [|].
    { destruct ty; eauto.
      destruct (typeof a1) eqn:Htype1; eauto; [].
      destruct (typeof a2) eqn:Htype2; eauto; [].
      destruct v1, v2 => //=. rewrite /=/Sop.sem_add//=/Sop.sem_binarith//= in H. inv H.
      edestruct IHHeval1 as [(Hsame&Hsame0)|Hv1]; eauto;
      edestruct IHHeval2 as [(Hsame'&Hsame0')|Hv2]; eauto.
      { left; split; eauto. intuition congruence. nra. }
      { right. rewrite Hsame. edestruct Hv2 as (v'&Heval'&f'&Heq1&Heq2).
        eexists. split.
        { econstructor; eauto.
          { eapply evaluation_preserved_no_target; eauto. }
          { rewrite //=. rewrite ?Heq1 ?Heq2. rewrite ?typeof_drop_const ?Htype1 ?Htype2 //=. }
        }
        { eexists; split; eauto. rewrite ?float_add_irf'. f_equal.
          rewrite ?IFR_IRF_inv ?IRF_IFR_inv.
          nra. }
      }
      { right. rewrite Hsame'. edestruct Hv1 as (v'&Heval'&f'&Heq1&Heq2).
        eexists. split.
        { econstructor; eauto.
          { eapply evaluation_preserved_no_target; eauto. }
          { rewrite //=. rewrite ?Heq1 ?Heq2. rewrite ?typeof_drop_const ?Htype1 ?Htype2 //=. }
        }
        { eexists; split; eauto. rewrite ?float_add_irf'. f_equal.
          rewrite ?IFR_IRF_inv ?IRF_IFR_inv.
          nra. }
      }
      { right.
        edestruct Hv1 as (v'&Heval'&f'&Heq1&Heq2).
        edestruct Hv2 as (v2&Heval2'&f2'&Heq12&Heq22).
        eexists. split.
        { econstructor; eauto.
          { rewrite //=. rewrite ?Heq1 ?Heq2 ?Heq12 ?Heq22.
            rewrite ?typeof_drop_const ?Htype1 ?Htype2 //=. }
        }
        { eexists; split; eauto. rewrite ?float_add_irf'. f_equal.
          rewrite ?IFR_IRF_inv ?IRF_IFR_inv.
          nra. }
      }
    }
    { destruct ty; eauto.
      destruct (typeof a1) eqn:Htype1; eauto; [].
      destruct (typeof a2) eqn:Htype2; eauto; [].
      destruct v1, v2 => //=. rewrite /=/Sop.sem_add//=/Sop.sem_binarith//= in H. inv H.
      edestruct IHHeval1 as [(Hsame&Hsame0)|Hv1]; eauto;
      edestruct IHHeval2 as [(Hsame'&Hsame0')|Hv2]; eauto.
      { left; split; eauto. intuition congruence. nra. }
      { right. rewrite Hsame. edestruct Hv2 as (v'&Heval'&f'&Heq1&Heq2).
        eexists. split.
        { econstructor; eauto.
          { eapply evaluation_preserved_no_target; eauto. }
          { rewrite //=. rewrite ?Heq1 ?Heq2. rewrite ?typeof_drop_const ?Htype1 ?Htype2 //=. }
        }
        { eexists; split; eauto. rewrite ?float_sub_irf'. f_equal.
          rewrite ?IFR_IRF_inv ?IRF_IFR_inv.
          nra. }
      }
      { right. rewrite Hsame'. edestruct Hv1 as (v'&Heval'&f'&Heq1&Heq2).
        eexists. split.
        { econstructor; eauto.
          { eapply evaluation_preserved_no_target; eauto. }
          { rewrite //=. rewrite ?Heq1 ?Heq2. rewrite ?typeof_drop_const ?Htype1 ?Htype2 //=. }
        }
        { eexists; split; eauto. rewrite ?float_sub_irf'. f_equal.
          rewrite ?IFR_IRF_inv ?IRF_IFR_inv.
          nra. }
      }
      { right.
        edestruct Hv1 as (v'&Heval'&f'&Heq1&Heq2).
        edestruct Hv2 as (v2&Heval2'&f2'&Heq12&Heq22).
        eexists. split.
        { econstructor; eauto.
          { rewrite //=. rewrite ?Heq1 ?Heq2 ?Heq12 ?Heq22.
            rewrite ?typeof_drop_const ?Htype1 ?Htype2 //=. }
        }
        { eexists; split; eauto. rewrite ?float_sub_irf'. f_equal.
          rewrite ?IFR_IRF_inv ?IRF_IFR_inv.
          nra. }
      }
    }
  - destruct a; try destruct b; eauto; [].
    destruct (math_fun_remap_const i) as [Hnormal|[Hcauchy|Hnone]].
    { destruct Hnormal as (->&->&->).
      right.
      destruct MATH. destruct GENV_NORMAL_LPDF as (l&Hnorm_symbol&Hnorm_funct). clear GENV_NORMAL_LUPDF.
      destruct MATHT. destruct GENV_NORMAL_LUPDF as (lu&Hnormu_symbol&Hnormu_funct).

      (* We first argue that eval in the source program computed the normal_lpdf *)
        inv Heval.
        {
          inv H4.
          inversion HNOSHADOW1 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          exploit (@gs_is_alloc Values.val); eauto.
          intros. congruence.
        }
        {
          inv H4.
          inversion HNOSHADOW2 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          exploit (@gs_is_alloc Floats.float); eauto.
          intros. congruence.
        }
        inv H5.
        { inv H1. }
        inv H4. subst.
        assert (loc = l) by congruence; subst.
        assert (AST.EF_external name sig = normal_lpdf_ef_external) as Heqf.
        { congruence. }
        rewrite Heqf in H3.
          exploit (normal_lpdf_ext_inv); eauto.
          intros (x&mean&variance&Hpos&Hvargs&Hvres).
          subst.

      eexists. split.
      {
        eapply eval_Ecall.
        eapply eval_Eglvalue.
        econstructor.
        {
          inversion HNOSHADOW2 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          congruence.
        }
        {
          inversion HNOSHADOW1 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          congruence.
        }
        eauto.
        { eapply deref_loc_reference; eauto. }
        eapply evaluation_preserved_no_target; eauto.
        eapply Hnormu_funct.
        2:{ eauto. }
        reflexivity.
        eapply normal_lupdf_ext_spec.
      }
      eexists. split; eauto. f_equal.
      rewrite IFR_IRF_inv.
      exploit (sqrt_lt_R0 2); first nra.
      exploit (sqrt_lt_R0 variance); first nra.
      specialize (PI_RGT_0). intros HPI.
      exploit (sqrt_lt_R0 (PI)); first nra.
      exploit (sqrt_lt_R0 (PI2)).
      { rewrite /PI in HPI. nra. }
      intros.
      rewrite /Rdiv ?sqrt_mult ?ln_mult ?ln_1 ?ln_Rinv; try nra; try eauto using exp_pos.
      { rewrite ?ln_mult ?ln_exp; try nra. }
      { repeat apply Rmult_lt_0_compat; auto. }
      { repeat apply Rmult_lt_0_compat; auto. }
      { apply Rinv_0_lt_compat; repeat apply Rmult_lt_0_compat; auto. }
      { apply Rinv_0_lt_compat; repeat apply Rmult_lt_0_compat; auto. }
      { ring_simplify. apply Rinv_0_lt_compat; repeat apply Rmult_lt_0_compat; auto. }
      rewrite /PI in HPI; nra.
    }
    { destruct Hcauchy as (->&->&->).
      right.
      destruct MATH. destruct GENV_CAUCHY_LPDF as (l&Hcauchy_symbol&Hcauchy_funct). clear GENV_CAUCHY_LUPDF.
      destruct MATHT. destruct GENV_CAUCHY_LUPDF as (lu&Hcauchyu_symbol&Hcauchyu_funct).

      (* We first argue that eval in the source program computed the cauchy_lpdf *)
        inv Heval.
        {
          inv H4.
          inversion HNOSHADOW1 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          exploit (@gs_is_alloc Values.val); eauto.
          intros. congruence.
        }
        {
          inv H4.
          inversion HNOSHADOW2 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          exploit (@gs_is_alloc Floats.float); eauto.
          intros. congruence.
        }
        inv H5.
        { inv H1. }
        inv H4. subst.
        assert (loc = l) by congruence; subst.
        assert (AST.EF_external name sig = cauchy_lpdf_ef_external) as Heqf.
        { congruence. }
        rewrite Heqf in H3.
          exploit (cauchy_lpdf_ext_inv); eauto.
          intros (x&mean&variance&Hpos&Hvargs&Hvres).
          subst.

      eexists. split.
      {
        eapply eval_Ecall.
        eapply eval_Eglvalue.
        econstructor.
        {
          inversion HNOSHADOW2 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          inversion Hnoshadow''' as [|??? Hnoshadow''''].
          congruence.
        }
        {
          inversion HNOSHADOW1 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          inversion Hnoshadow''' as [|??? Hnoshadow''''].
          congruence.
        }
        eauto.
        { eapply deref_loc_reference; eauto. }
        eapply evaluation_preserved_no_target; eauto.
        eapply Hcauchyu_funct.
        2:{ eauto. }
        reflexivity.
        eapply cauchy_lupdf_ext_spec.
      }
      eexists. split; eauto. f_equal.
      rewrite IFR_IRF_inv.
      exploit (sqrt_lt_R0 2); first nra.
      exploit (sqrt_lt_R0 variance); first nra.
      specialize (PI_RGT_0). intros HPI.
      exploit (sqrt_lt_R0 (PI)); first nra.
      assert (0 < PI2).
      { rewrite /PI in HPI. nra. }
      exploit (sqrt_lt_R0 (PI2)); first nra.
      assert (0 < 1 + ((x - mean) * / variance) ^ 2).
      { specialize (pow2_ge_0 ((x - mean) * / variance)).
        intros. nra. }
      rewrite /Rdiv ?sqrt_mult ?ln_mult ?ln_1 ?ln_Rinv; try nra; try eauto using exp_pos;
        rewrite ?ln_mult ?ln_exp; try nra.
      { repeat apply Rmult_lt_0_compat; auto. nra. }
      { apply Rinv_0_lt_compat; nra. }
      { apply Rinv_0_lt_compat; repeat apply Rmult_lt_0_compat; auto. nra. }
    }
    { destruct Hnone as (->&->); eauto. }
  - inv H; eauto.
  - inv H; eauto.
  - inv H; eauto.
Qed.

Lemma eval_expr_preserved:
  forall en m pm t t' e v,
  check_no_target_expr e = Some tt ->
  eval_expr ge en m pm t e v ->
  eval_expr tge en m pm t' e v.
Proof.
  intros.
  eapply evaluation_preserved_no_target; eauto.
Qed.

Lemma eval_glvalue_preserved:
  forall en m pm t t' e loc ofs,
  check_no_target_expr e = Some tt ->
  eval_glvalue ge en m pm t e loc ofs ->
  eval_glvalue tge en m pm t' e loc ofs.
Proof.
  intros.
  eapply evaluation_preserved_no_target; eauto.
Qed.

Lemma eval_llvalue_preserved:
  forall en m pm t t' e loc ofs,
  check_no_target_expr e = Some tt ->
  eval_llvalue ge en m pm t e loc ofs ->
  eval_llvalue tge en m pm t' e loc ofs.
Proof.
  intros.
  eapply evaluation_preserved_no_target; eauto.
Qed.

Lemma eval_exprlist_preserved:
  forall en m pm t t' el vl,
  check_no_target_exprlist el = Some tt ->
  eval_exprlist ge en m pm t el vl ->
  eval_exprlist tge en m pm t' el vl.
Proof.
  intros.
  eapply evaluation_preserved_no_target; eauto.
Qed.

Lemma assign_loc_preserved ty m blk ofs v m2 :
  assign_loc ge ty m blk ofs v m2 ->
  assign_loc tge ty m blk ofs v m2.
Proof.
  inversion 1. econstructor; eauto.
Qed.

Lemma assign_global_locs_preserved bs m1 vs m2 :
  assign_global_locs ge bs m1 vs m2 ->
  assign_global_locs tge bs m1 vs m2.
Proof.
  induction 1; econstructor; eauto.
  - rewrite symbols_preserved; eauto.
  - inversion H0; eapply assign_loc_value; eauto.
Qed.

Lemma reserve_global_params_preserved bs m1 m2 :
  reserve_global_params bs m1 m2 ->
  reserve_global_params bs m1 m2.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma assign_global_params_preserved bs m1 vs m2 :
  assign_global_params bs m1 vs m2 ->
  assign_global_params bs m1 vs m2.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma set_global_params_preserved ids bs m1 vs m2 :
  set_global_params ids bs vs m1 m2 ->
  set_global_params ids bs vs m1 m2.
Proof.
  intros (?&?&?). eexists; split;
    eauto using reserve_global_params_preserved, assign_global_params_preserved.
Qed.

Lemma data_vars_preserved :
  pr_data_vars tprog = pr_data_vars prog.
Proof.
  unfold match_prog in TRANSL. intuition.
Qed.

Lemma parameters_vars_preserved :
  pr_parameters_vars tprog = pr_parameters_vars prog.
Proof.
  unfold match_prog in TRANSL. intuition.
Qed.

Lemma parameters_ids_preserved :
  pr_parameters_ids tprog = pr_parameters_ids prog.
Proof.
  unfold pr_parameters_ids. rewrite parameters_vars_preserved. auto.
Qed.


(* Simulation in the case where additive const doesn't change the program *)
Section nochange.

Variable no_change_model :
  ∃ bprog btprog f,
  Genv.find_symbol ge $"model" = Some bprog /\
  Genv.find_funct_ptr ge bprog = Some (Ctypes.Internal f) /\
  Genv.find_symbol tge $"model" = Some btprog /\
  Genv.find_funct_ptr tge btprog = Some (Ctypes.Internal f).

Definition match_states_nochange: state -> state -> Prop := λ s1 s2, s1 = s2.

Lemma transf_initial_states_nochange:
  forall S1, initial_state prog data params S1 ->
  exists S2, initial_state tprog data params S2 /\ match_states_nochange S1 S2.
Proof.
  intros S1 Hinit. inv Hinit.
  edestruct no_change_model as (bprog&btprog&f'&?&?&?&?).
  rewrite /ge0 in H0 H1.
  rewrite /ge in H5 H6.
  assert (b = bprog) by congruence; subst.
  assert (f = f') by congruence; subst.
  eexists. split; last by econstructor.
  econstructor; eauto.
  destruct TRANSL as (TRANSL'&_).
  eapply (Genv.init_mem_match TRANSL'); eauto.
  eapply assign_global_locs_preserved. rewrite data_vars_preserved; eauto.
  eapply set_global_params_preserved; rewrite parameters_vars_preserved parameters_ids_preserved. eauto.
Qed.

Lemma step_simulation_nochange:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states_nochange S1 S1' ->
  exists S2', step tge S1' t S2' /\ match_states_nochange S2 S2'.
Proof.
  induction 1; intros S1' MS; inversion MS; simpl in *; subst;
  try (eexists; split; econstructor; eauto; done);
  try (eexists; split; last reflexivity; econstructor; eauto; eapply evaluation_preserved_same; eauto; done).
  - eexists. split; last reflexivity.
    { eapply step_assign_mem; eauto.
      * eapply evaluation_preserved_same; eauto.
      * eapply evaluation_preserved_same; eauto.
      * apply assign_loc_preserved; auto.
    }
  - eexists. split; last reflexivity.
    econstructor; eauto; try (eapply evaluation_preserved_same; eauto).
    { exploit functions_translated; eauto. }
    { eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved. }
Qed.

Lemma transf_final_states_nochange:
  forall S1 S2 t r, match_states_nochange S1 S2 -> final_state t S1 r -> final_state t S2 r.
Proof.
  intros S1 S2 t r Hmatch Hfinal. inv Hfinal; inv Hmatch.
  { econstructor. auto. }
  { econstructor. auto. }
Qed.

Theorem transf_program_correct_nochange t:
  forward_simulation (Ssemantics.semantics prog data params t) (Ssemantics.semantics tprog data params t).
Proof.
  eapply forward_simulation_step.
  eapply senv_preserved.
  eexact transf_initial_states_nochange.
  intros. eapply transf_final_states_nochange; eauto.
  exact step_simulation_nochange.
Qed.

End nochange.

Section change.

Variable model_fn : function.

Variable change_model :
  ∃ bprog btprog body,
  Genv.find_symbol ge $"model" = Some bprog /\
  Genv.find_funct_ptr ge bprog = Some (Ctypes.Internal model_fn) /\
  transf_function_body model_fn = Some body /\
  Genv.find_symbol tge $"model" = Some btprog /\
  Genv.find_funct_ptr tge btprog = Some (Ctypes.Internal (mkfunction body model_fn.(fn_vars))).

Inductive transf_const_match : _ -> _ -> _ -> Prop :=
  | transf_const_change : forall s s' r
    (TRS: transf_statement s = Some s')
    (CONST: compute_const_statement' s = Some r),
    transf_const_match s s' r
  | transf_const_same : forall s,
    transf_const_match s s 0.

Inductive match_cont: cont -> cont -> list (AST.ident * Integers.Int.int) -> R -> Prop :=
  | match_Kseq_change: forall s s' k k' iv r rnew r'
      (MCONT: match_cont k k' iv r)
      (TRSC: transf_const_match s s' rnew)
      (NT: check_no_target_statement s = Some tt)
      (NA: Forall (λ '(i, v), check_no_assign i s = true) iv)
      (REQ: r' = r + rnew),
      match_cont (Kseq s k) (Kseq s' k') iv r'
  | match_Kstop:
      match_cont Kstop Kstop nil 0
  | match_Kfor_match: forall id e2 s k k' iv r
      (MCONT: match_cont k k' iv r)
      (NT: check_no_target_statement s = Some tt)
      (NTE: check_no_target_expr e2 = Some tt)
      (NA: Forall (λ '(i, v), check_no_assign i s = true) iv)
      (NAI: Forall (λ '(i, v),
           (match Pos.eq_dec id i return bool with | left _ => false | _ => true end) = true) iv),
      match_cont (Kfor id e2 s k) (Kfor id e2 s k') iv r
  | match_Kfor_change: forall id ub s s' k k' iv r idval rloop
      (MCONT: match_cont k k' iv r)
      (TRS: transf_statement s = Some s')
      (NT: check_no_target_statement s = Some tt)
      (NA: Forall (λ '(i, v), check_no_assign i s = true) ((id, idval) :: iv))
      (CONST: compute_const_statement' s = Some rloop)
      (LE: (Integers.Int.unsigned idval <= Integers.Int.unsigned ub)%Z)
      (NAI: Forall (λ '(i, v),
           (match Pos.eq_dec id i return bool with | left _ => false | _ => true end) = true) iv),
      match_cont (Kfor id (Econst_int ub Bint) s k) (Kfor id (Econst_int ub Bint) s' k')
        ((id, idval) :: iv) (IZR (Integers.Int.unsigned ub - Integers.Int.unsigned idval) * rloop + r).

(* Should run compute_const_statement on full body *)

Definition env_match_vals (en: env) (ivs: list (AST.ident * Integers.Int.int)) : Prop :=
  Forall (λ '(id, k), ParamMap.get en id 0 = Some (Values.Vint k)) ivs.

Definition compute_const_function (f: Stanlight.function) : R :=
  let res := (do _ <- list_option_map (vars_check_shadow) (f.(fn_vars));
              do _ <- check_no_target_statement f.(fn_body);
    compute_const_statement' f.(fn_body)) in
  match res with
  | None => 0
  | Some r => r
  end.

Inductive match_states: state -> state -> Prop :=
  | match_start_states: forall s s' t e m pm
      (FN: s = (fn_body model_fn))
      (TRS: s' = (fn_body (transf_function model_fn)))
      (NT: check_no_target_statement s = Some tt)
      (ENOSHADOW: no_shadow_pdflib e)
      (PMNOSHADOW: no_shadow_pdflib pm),
      match_states (Start model_fn s t Kstop e m pm) (Start (transf_function model_fn) s' t Kstop e m pm)
  | match_regular_states: forall s s' t t' k k' e m pm iv rk rs
      (MCONT: match_cont k k' iv rk)
      (TRSC: transf_const_match s s' rs)
      (NT: check_no_target_statement s = Some tt)
      (NA: Forall (λ '(i, v), check_no_assign i s = true) iv)
      (DIFF: IFR t - IFR t' = compute_const_function model_fn - rs - rk)
      (ENV: env_match_vals e iv)
      (ENOSHADOW: no_shadow_pdflib e)
      (PMNOSHADOW: no_shadow_pdflib pm),
      match_states (State model_fn s t k e m pm) (State (transf_function model_fn) s' t' k' e m pm)
  | match_return_states: forall t t' e m pm
      (DIFF: IFR t - IFR t' = compute_const_function model_fn),
      match_states (Return model_fn t e m pm) (Return (transf_function model_fn) t' e m pm).

Lemma transf_statement_some_compute_const s s' :
  transf_statement s = Some s' ->
  ∃ r, compute_const_statement' s = Some r.
Proof.
  revert s'.
  induction s => //=; eauto => s' Heq.
  { apply some_bind_inversion in Heq as (s1'&Heqs1'&Hrest).
    apply some_bind_inversion in Hrest as (s2'&Heqs2'&Hrest).
    inv Hrest.
    exploit IHs1; eauto. intros (r1&Hr1).
    exploit IHs2; eauto. intros (r2&Hr2).
    eexists => //=. rewrite Hr1 Hr2 //=.
  }
  {
    destruct e; inv Heq; eauto.
    destruct b; eauto.
    destruct e0; inv H0; eauto.
    destruct b; eauto.
    destruct (check_no_assign i s); eauto.
    monadInv H1. exploit IHs; eauto. intros (r&->). eexists.
    eauto.
  }
Qed.

Lemma compute_const_some_transf_statement s r :
  compute_const_statement' s = Some r ->
  ∃ s', transf_statement s = Some s'.
Proof.
  revert r.
  induction s => //=; eauto => s' Heq.
  { apply some_bind_inversion in Heq as (s1'&Heqs1'&Hrest).
    apply some_bind_inversion in Hrest as (s2'&Heqs2'&Hrest).
    inv Hrest.
    exploit IHs1; eauto. intros (r1&Hr1).
    exploit IHs2; eauto. intros (r2&Hr2).
    eexists => //=. rewrite Hr1 Hr2 //=.
  }
  {
    destruct e; inv Heq; eauto.
    destruct b; eauto.
    destruct e0; inv H0; eauto.
    destruct b; eauto.
    destruct (check_no_assign i s); eauto.
    monadInv H1. exploit IHs; eauto. intros (r&->). eexists.
    eauto.
  }
Qed.

Lemma transf_statement_none_compute_const s :
  transf_statement s = None ->
  compute_const_statement' s = None.
Proof.
  intros. destruct (compute_const_statement' s) eqn:Hnone; auto.
  exfalso. exploit (compute_const_some_transf_statement); eauto. intros (?&?); congruence.
Qed.

Lemma store_env_match_vals e id ofs v e' iv
  (NA: Forall (λ '(i, v),
           (match Pos.eq_dec id i return bool with | left _ => false | _ => true end) = true) iv):
  env_match_vals e iv ->
  store e id ofs v = Some e' ->
  env_match_vals e' iv.
Proof.
  rewrite /env_match_vals => Hforall Hstore.
  revert e e' Hforall Hstore.
  induction iv as [| (?&?) iv'].
  { intros e e' Hforall Hstore. econstructor. }
  { intros e e' Hforall Hstore. inv Hforall.
    econstructor; last first.
    { eapply IHiv'; eauto. inv NA; eauto. }
    inv NA. destruct (Pos.eq_dec).
    { subst. congruence. }
    erewrite gsto; eauto.
  }
Qed.

Lemma eval_expr_const_int_inv genv e m pm t i1 v1  :
  eval_expr genv e m pm t (Econst_int i1 Bint) (Values.Vint v1) ->
  i1 = v1.
Proof. inversion 1; subst; eauto. inv H0. inv H0. Qed.

Variable prog_genv_has_mathlib :
  genv_has_mathlib (globalenv prog).

Lemma transf_const_match_skip_inv s' rs :
  transf_const_match Sskip s' rs ->
  s' = Sskip /\ rs = 0.
Proof.
  intros TRSC. inv TRSC; eauto. inv TRS; eauto. inv CONST. eauto.
Qed.

Lemma transf_const_match_for_inv i a1 a2 s s' rs :
  transf_const_match (Sfor i a1 a2 s) s' rs ->
  ((s' = Sfor i a1 a2 s /\ rs = 0) ∨
          (∃ i1 i2 sbody' rbody,
              s' = Sfor i a1 a2 sbody' /\
              a1 = Econst_int i1 Bint /\ a2 = Econst_int i2 Bint /\
                                   check_no_assign i s = true /\
                                   transf_statement s = Some sbody' /\
                                   compute_const_statement' s = Some rbody /\
                                   transf_const_match s sbody' rbody /\
                                   rs = ((rbody * IZR (Z.max (Integers.Int.unsigned i2 -
                                                                Integers.Int.unsigned i1 + 1)%Z 0)%Z)))).
Proof.
  intros TRSC.
  inv TRSC; last by eauto.
  { simpl in CONST.
    destruct a1; try (inv TRS; inv CONST; left; eauto; done); [].
    simpl in TRS.
    destruct b; try (inv TRS; inv CONST; left; eauto; done); [].
    destruct a2; try (inv TRS; inv CONST; left; eauto; done); [].
    destruct b; try (inv TRS; inv CONST; left; eauto; done); [].
    destruct (check_no_assign i s); last first.
    { inv CONST. inv TRS. eauto. }
    right. monadInv TRS. monadInv CONST.
    do 4 eexists.
    { repeat split; eauto.
      econstructor; eauto. }
  }
Qed.

Lemma transf_const_match_fun f :
  transf_const_match (fn_body f) (fn_body (transf_function f)) (compute_const_function f).
Proof.
  clear.
  rewrite /transf_function/transf_function_body/compute_const_function.
  destruct (list_option_map _ _); last first.
  { rewrite /=. apply transf_const_same. }
  destruct (check_no_target_statement ); last first.
  { rewrite /=. apply transf_const_same. }
  destruct (transf_statement (fn_body f)) eqn:Htransf.
  { exploit transf_statement_some_compute_const; eauto. intros (r&Hcompute).
    rewrite Hcompute. simpl. econstructor; eauto. }
  { exploit transf_statement_none_compute_const; eauto. intros Hcompute.
    rewrite Hcompute. eapply transf_const_same. }
Qed.

Lemma list_option_map_inversion {A B: Type} (f: A -> option B) (l: list A) (l' : list B) :
  list_option_map f l = Some l' -> list_forall2 (λ x y, f x = Some y) l l'.
Proof.
  revert l'.
  induction l; eauto.
  { simpl. inversion 1; subst. econstructor; eauto. }
  { intros l'.
    simpl. intros Heq.
    apply some_bind_inversion in Heq as (b'&?&Hrest).
    apply some_bind_inversion in Hrest as (l''&Hrec&Hrest).
    eapply IHl in Hrec. destruct l' as [|]; inv Hrest; [].
    econstructor; eauto.
  }
Qed.

Lemma vars_check_shadow_ok id b xt:
  vars_check_shadow (id, b) = Some xt ->
  ¬ In id pdf_idents.
Proof.
  intros Hin.
  unfold vars_check_shadow in Hin.
  destruct (forallb _ _) eqn:Hforallb; last by inv Hin.
  rewrite forallb_forall in Hforallb * => Hforallb.
  intros Hin'. assert (In id (pdf_idents ++ math_idents)) as Hin''.
  { apply in_or_app; eauto. }
  eapply Hforallb in Hin''.
  destruct (Pos.eq_dec id id); inv Hin''.
  congruence.
Qed.

Lemma transf_initial_states:
  forall S1, initial_state prog data params S1 ->
  exists S2, initial_state tprog data params S2 /\ match_states S1 S2.
Proof.
  intros S1 Hinit. inv Hinit.
  edestruct change_model as (bprog&btprog&f'&Hfinds&Hfindp&Htransf&?&?).
  rewrite /ge0 in H0 H1.
  rewrite /ge in Hfinds Hfindp.
  assert (b = bprog) by congruence; subst.
  assert (f = model_fn) by congruence; subst.
  eexists. split.
  {
    econstructor; eauto.
    destruct TRANSL as (TRANSL'&_).
    eapply (Genv.init_mem_match TRANSL'); eauto.
    simpl. eapply assign_global_locs_preserved. rewrite data_vars_preserved; eauto.
    eapply set_global_params_preserved; rewrite parameters_vars_preserved parameters_ids_preserved. eauto.
  }
  {
    simpl.
    assert ({| fn_body := f'; fn_vars := fn_vars model_fn |} = transf_function (model_fn)) as ->.
    { rewrite /transf_function. rewrite Htransf //. }

    econstructor; eauto.
    { rewrite /transf_function. rewrite Htransf //=. }
    { unfold transf_function_body in Htransf.
      { apply some_bind_inversion in Htransf as (s1'&Heqs1'&Hrest).
        apply some_bind_inversion in Hrest as ([]&Heqs2'&Hrest).
        eauto.
      }
    }
    { unfold transf_function_body in Htransf.
      { apply some_bind_inversion in Htransf as (s1'&Heqs1'&Hrest).
        apply Forall_forall. intros x Hin.
        eapply list_option_map_inversion in Heqs1' as EQ.

        destruct (is_id_alloc e x) as [] eqn:Hgetenv; auto.
        eapply alloc_variables_in_env in Hgetenv; eauto.
        destruct Hgetenv as [(?&Hin')|Hfalso].
        {
          eapply list_forall2_in_left in EQ as (?&?&Hin''); eauto.
          apply vars_check_shadow_ok in Hin''.
          intuition.
        }
        { rewrite is_id_empty in Hfalso; congruence. }
      }
    }
    {
      admit.
    }
  }
Abort.

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inversion MS; simpl in *; subst.
  - (* Start *)
    eexists.
    split.
    { econstructor. }
    {
      econstructor; eauto.
      { econstructor. }
      { eapply transf_const_match_fun. }
      { nra. }
      econstructor.
    }
  - (* Return *)
    inv MCONT.
    edestruct (transf_const_match_skip_inv) as (?&?); eauto. subst.
    eexists; split.
    { econstructor. }
    { econstructor. nra. }
  - (* Skip *)
    edestruct (transf_const_match_skip_inv) as (?&?); eauto. subst.
    inv MCONT.
    eexists. split.
    { econstructor. }
    { econstructor; eauto. nra. }
  - (* Sequence *)
    apply some_bind_inversion in NT as ([]&?&NT).
    apply some_bind_inversion in NT as ([]&?&NT).
    monadInv NT.
    assert (∃ s1' s2' rs1 rs2, s' = (Ssequence s1' s2') /\
                               rs = rs1 + rs2 /\
                               transf_const_match s1 s1' rs1 /\
                                 transf_const_match s2 s2' rs2)
    as (s1'&s2'&rs1&rs2&Heq'&Hrs&Hmatch1&Hmatch2).
    { inv TRSC.
      { simpl in TRS.
        apply some_bind_inversion in TRS as (s1'&Heqs1'&TRS).
        apply some_bind_inversion in TRS as (s2'&Heqs2'&TRS).
        simpl in CONST.
        apply some_bind_inversion in CONST as (r1&Hcompute1&CONST).
        apply some_bind_inversion in CONST as (r2&Hcompute2&CONST).
        monadInv TRS. do 4 eexists; split; eauto; split => //=.
        inv CONST; auto.
        split; econstructor; eauto.
      }
      { exists s1, s2, 0, 0. split; auto. split; auto. nra.
        split; eapply transf_const_same. }
    }
    subst.
    { eexists. split.
      { econstructor. }
      { econstructor; try eassumption.
        { econstructor; try eassumption.
          { eapply Forall_impl; last eapply NA.
            intros (?&?). apply andb_prop. }
          reflexivity.
        }
        { eapply Forall_impl; last eapply NA.
          intros (?&?). apply andb_prop. }
        { nra. }
      }
    }
  - (* Assignment *)
    apply some_bind_inversion in NT as ([]&?&NT).
    apply some_bind_inversion in NT as ([]&?&NT).
    monadInv NT.
    assert (s' = Sassign a1 None a2 /\ rs = 0) as (->&->).
    { inv TRSC; eauto. inv TRS. inv CONST. auto. }
    eexists.
    split.
    { econstructor.
      eapply eval_llvalue_preserved; eauto.
      eapply eval_expr_preserved; eauto.
      eauto.
    }
    { econstructor; eauto.
      { eapply transf_const_same. }
      { clear. induction iv => //=. econstructor; eauto. destruct a; auto. }
      eapply store_env_match_vals.
      { inv H; eauto. }
      { eauto. }
      { eauto. }
      { eapply no_shadow_pdflib_store; eauto. }
    }
  - (* Assignment *)
    apply some_bind_inversion in NT as ([]&?&NT).
    apply some_bind_inversion in NT as ([]&?&NT).
    monadInv NT.
    assert (s' = Sassign a1 None a2 /\ rs = 0) as (->&->).
    { inv TRSC; eauto. inv TRS. inv CONST. auto. }
    eexists.
    split.
    {
      eapply step_assign_mem.
      { eapply eval_glvalue_preserved; eauto. }
      { eapply eval_expr_preserved; eauto. }
      { eauto. }
      { eapply assign_loc_preserved; eauto. }
    }
    { econstructor; eauto; rewrite //=.
      { eapply transf_const_same. }
      clear. induction iv as [| (?&?)]; eauto. }
  - (* Conditional statement *)
    apply some_bind_inversion in NT as ([]&?&NT).
    apply some_bind_inversion in NT as ([]&?&NT).
    apply some_bind_inversion in NT as ([]&?&NT).
    assert (s' = Sifthenelse a s1 s2 /\ rs = 0) as (->&->).
    { inv TRSC; eauto. inv TRS. inv CONST. auto. }
    eexists. split.
    {
      econstructor.
      { eapply eval_expr_preserved; eauto. }
      { eauto. }
    }
    econstructor; eauto.
    { eapply transf_const_same. }
    { destruct b; eauto. }
    { eapply Forall_impl; last eapply NA.
      intros (?&?). destruct b; apply andb_prop. }
  - (* Target *)
    inv TRSC.
    {
      monadInv TRS.
      exploit evaluation_drop_const_aux; eauto.
      destruct 1 as [Hid|Hex].
      {
        destruct Hid as (Hconst&Hcompute).
        eexists. split.
        {
          rewrite Hconst.
          econstructor; eauto.
          { eapply eval_expr_preserved; eauto. }
        }
        econstructor; eauto.
        { eapply transf_const_same. }
        { rewrite ?float_add_irf' ?IFR_IRF_inv.
          ring_simplify. inv CONST. nra. }
      }
      {
        destruct Hex as (v'&Heval&(f'&Hv'&Hf')).
        subst.
        eexists. split.
        {
          econstructor. eauto.
        }
        econstructor; eauto.
        { eapply transf_const_same. }
        { rewrite ?float_add_irf' ?IFR_IRF_inv.
          ring_simplify. inv CONST. nra. }
      }
    }
    { eexists. split.
      { econstructor; eauto. eapply eval_expr_preserved; eauto. }
      { econstructor; eauto.
        { eapply transf_const_same. }
        { rewrite ?float_add_irf' ?IFR_IRF_inv.
          ring_simplify. nra. }
      }
    }
  - (* Tilde *)
    (* Impossible case *)
    congruence.
  - (* For *)
    apply some_bind_inversion in NT as ([]&?&NT).
    apply some_bind_inversion in NT as ([]&?&NT).
    apply some_bind_inversion in NT as ([]&?&NT).
    edestruct (transf_const_match_for_inv) as [Hid|Hchange]; first eassumption.
    { destruct Hid as [-> ->]. eexists. split.
      { econstructor; eauto.
        { eapply eval_llvalue_preserved; eauto. }
        { eapply eval_expr_preserved; eauto. }
        { eapply eval_expr_preserved; eauto. }
      }
      econstructor.
      { econstructor; try eauto.
        { eapply Forall_impl; last eapply NA.
          intros (?&?). destruct (Pos.eq_dec p i); try inversion 1; auto. }
        { eapply Forall_impl; last eapply NA.
          intros (?&?).
          destruct (Pos.eq_dec p i); try inversion 1; auto.
          destruct (Pos.eq_dec i p); try inversion 1; auto.
          congruence.
        }
      }
      eapply transf_const_same.
      eauto.
      { eapply Forall_impl; last eapply NA.
        intros (?&?). destruct (Pos.eq_dec p i); try inversion 1; auto. }
      { eauto. }
      eapply store_env_match_vals; eauto.
      { inv H.
        eapply Forall_impl; last eapply NA.
        intros (?&?).
        destruct (Pos.eq_dec p loc); try inversion 1; auto.
        destruct (Pos.eq_dec loc p); try congruence.
      }
      { eapply no_shadow_pdflib_store; eauto. }
      { eauto. }
    }
    {
      destruct Hchange as (i1&i2&sbody'&rbody&->&->&->&Hcheck&Htransf'&Hcomp&Htransf&Hrs).
      assert (i1 = v1) as ->.
      { eapply eval_expr_const_int_inv; eauto. }
      assert (i2 = v2) as ->.
      { eapply eval_expr_const_int_inv; eauto. }

      subst.
      eexists. split.
      { econstructor; eauto.
        { eapply eval_llvalue_preserved; eauto. }
        { eapply eval_expr_preserved; eauto. }
        { eapply eval_expr_preserved; eauto. }
      }
      econstructor.
      { eapply (match_Kfor_change) with (idval := v1); eauto.
        { econstructor; eauto.
          eapply Forall_impl; last eapply NA.
          intros (?&?).
          destruct (Pos.eq_dec i0 i); try inversion 1; auto.
        }
        { eapply Forall_impl; last eapply NA.
          intros (?&?).
          destruct (Pos.eq_dec p i); try inversion 1; auto.
          destruct (Pos.eq_dec i p); try inversion 1; auto.
          congruence.
        }
      }
      eauto.
      eauto.
      { econstructor; eauto.
        { eapply Forall_impl; last eapply NA.
          intros (?&?).
          destruct (Pos.eq_dec i0 i); try inversion 1; auto.
        }
      }
      subst.
      rewrite Z.max_l in DIFF; last first.
      { lia. }
      rewrite DIFF. ring_simplify. rewrite ?plus_IZR. nra.
      inv H.
      econstructor.
      { eapply gsts; eauto. }
      eapply store_env_match_vals; eauto.
      { eapply Forall_impl; last eapply NA.
        intros (?&?).
        destruct (Pos.eq_dec p loc); try inversion 1; auto.
        destruct (Pos.eq_dec loc p); try inversion 1; auto.
        congruence.
      }
      { eapply no_shadow_pdflib_store; eauto. }
      { eauto. }
    }
  - (* For *)
    apply some_bind_inversion in NT as ([]&?&NT).
    apply some_bind_inversion in NT as ([]&?&NT).
    apply some_bind_inversion in NT as ([]&?&NT).
    assert (∃ sbody', (s' = Sfor i a1 a2 sbody') /\ rs = 0) as (sbody'&->&Hrs).
    { inv TRSC; last by eauto.
      { simpl in CONST.
        destruct a1; try (inv TRS; inv CONST; eexists; eauto; done).
        simpl in TRS.
        destruct b; try (inv TRS; inv CONST; eexists; eauto; done); [].
        destruct a2; try (inv TRS; inv CONST; eexists; eauto; done); [].
        destruct b; try (inv TRS; inv CONST; eexists; eauto; done); [].
        destruct (check_no_assign i s); last first.
        { inv CONST. inv TRS. eauto. }
        monadInv TRS. monadInv CONST.
        eexists. split; eauto.
        assert (i0 = v1) as ->.
        { eapply eval_expr_const_int_inv; eauto. }
        assert (i1 = v2) as ->.
        { eapply eval_expr_const_int_inv; eauto. }
        rewrite Z.max_r; first nra.
        lia.
      }
    }
    eexists. split.
    {
      eapply step_for_start_false; eauto.
      { eapply eval_expr_preserved; eauto. }
      { eapply eval_expr_preserved; eauto. }
    }
    { econstructor; eauto.
      { subst. eapply transf_const_same. }
      { clear. induction iv as [|(?&?)] => //=; econstructor; eauto. }
    }
  - (* For iter true *)
    assert (Integers.Ptrofs.intval ofs = 0%Z) as Heq0.
    {
      inv H.
      assert ((Integers.Ptrofs.intval Integers.Ptrofs.zero)
              =  ((Integers.Ptrofs.unsigned Integers.Ptrofs.zero))) as Hfold.
      { rewrite //=. }
      rewrite Hfold.
      rewrite Integers.Ptrofs.unsigned_zero.
      auto.
    }
    assert (Integers.Int.unsigned (Integers.Int.add v1 Integers.Int.one) =
           Integers.Int.unsigned v1 + 1)%Z as Heqz.
    {
      rewrite Integers.Int.unsigned_add_carry.
      assert (Integers.Int.unsigned (Integers.Int.add_carry v1 Integers.Int.one Integers.Int.zero) = 0%Z) as ->.
      {
        rewrite /Integers.Int.add_carry.
        rewrite ?Integers.Int.unsigned_zero.
        rewrite ?Integers.Int.unsigned_one.
        destruct zlt as [Hlt|Hnlt].
        {rewrite ?Integers.Int.unsigned_zero //. }
        { specialize (Integers.Int.unsigned_range v2). lia. }
      }
        rewrite ?Integers.Int.unsigned_one. lia.
    }

    edestruct (transf_const_match_skip_inv) as (?&?); eauto. subst.
    inv MCONT.
    {
      eexists. split.
      {
        eapply step_for_iter_true; eauto.
        { eapply eval_llvalue_preserved; eauto. }
        { eapply eval_expr_preserved; eauto. }
      }
      econstructor; eauto.
      { econstructor; eauto. }
      { apply transf_const_same. }
      { eapply store_env_match_vals; last eassumption; eauto.
        { inv H; subst. eauto. }
      }
      { eapply no_shadow_pdflib_store; eauto. }
    }
    {
      assert (v1 = idval) as ->.
      {
        unfold env_match_vals in ENV.
        rewrite Heq0 in H0. inv ENV. inv H. congruence.
      }
      eexists. split.
      {
        eapply step_for_iter_true; eauto.
        { eapply eval_llvalue_preserved; eauto. }
        { eapply eval_expr_preserved; eauto. }
      }
      econstructor.
      {
        eapply match_Kfor_change with (idval := (Integers.Int.add idval Integers.Int.one)); eauto.
        { inv NA0; econstructor; eauto. }
        { rewrite Heqz. exploit eval_expr_const_int_inv; eauto => ->. lia. }
      }
      { eapply transf_const_change; eauto. }
      { eauto. }
      { inv NA0; econstructor; eauto. }
      { rewrite DIFF.
        rewrite Heqz.
        rewrite ?minus_IZR.
        rewrite ?plus_IZR. ring_simplify.
        ring.
      }
      { econstructor.
        { eapply gsts; eauto. inv H. rewrite Heq0 in H2. eauto. }
        inv ENV. inv H.
        eapply store_env_match_vals; [| eassumption|]; eauto.
      }
      { eapply no_shadow_pdflib_store; eauto. }
      { eauto. }
    }
  - assert (Integers.Ptrofs.intval ofs = 0%Z) as Heq0.
    {
      inv H.
      assert ((Integers.Ptrofs.intval Integers.Ptrofs.zero)
              =  ((Integers.Ptrofs.unsigned Integers.Ptrofs.zero))) as Hfold.
      { rewrite //=. }
      rewrite Hfold.
      rewrite Integers.Ptrofs.unsigned_zero.
      auto.
    }
    edestruct (transf_const_match_skip_inv) as (?&?); eauto. subst.
    inv MCONT.
    { eexists. split.
      { eapply step_for_iter_false.
        { eapply eval_llvalue_preserved; eauto. }
        { eauto. }
        { eapply eval_expr_preserved; eauto. }
        { auto. }
      }
      { econstructor; eauto. }
    }
    { eexists. split.
      { eapply step_for_iter_false.
        { eapply eval_llvalue_preserved; eauto. }
        { eauto. }
        { eapply eval_expr_preserved; eauto. }
        { auto. }
      }
      { econstructor; eauto.
        { simpl. clear. induction iv0 as [| (?&?)]; econstructor; eauto. }
        { rewrite DIFF.
          assert ((Integers.Int.unsigned ub - Integers.Int.unsigned idval) = 0)%Z as ->.
          {
            assert (v1 = idval) as ->.
            {
              unfold env_match_vals in ENV.
              rewrite Heq0 in H0. inv ENV. inv H. congruence.
            }
           exploit eval_expr_const_int_inv; eauto => Heq.
           subst. lia.
          }
          nra.
        }
        inv ENV; eauto.
      }
    }
Qed.

Lemma transf_final_states:
  forall S1 S2 t r, match_states S1 S2 -> final_state t S1 r ->
                    final_state (IRF (IFR t - compute_const_function model_fn)) S2 r.
Proof.
  intros S1 S2 t r Hmatch Hfinal. inv Hfinal; inv Hmatch.
  { constructor. rewrite -DIFF. rewrite -[a in _ = a](IRF_IFR_inv t'). f_equal. ring. }
  { constructor. rewrite -DIFF. rewrite -[a in _ = a](IRF_IFR_inv t').
    intros Heq%IRF_inj. assert (IFR t = IFR t0) as Hfr by nra.
    apply IFR_inj in Hfr. congruence. }
Qed.

End change.

Theorem transf_program_correct t:
  forward_simulation (Ssemantics.semantics prog data params t) (Ssemantics.semantics tprog data params t).
Proof.
Abort.

End PRESERVATION.

Section DENOTATIONAL_PRESERVATION.

Variable prog: program.
Variable tprog: program.
Variable TRANSL: match_prog prog tprog.

Theorem denotational_preserved :
  denotational_refinement tprog prog.
Proof.
Abort.

End DENOTATIONAL_PRESERVATION.

Global Instance TransfSamplingLink : TransfLink match_prog.
Proof.
Admitted.
