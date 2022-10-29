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
  | Sfor i (Econst_int i1 b1) (Econst_int i2 b2) s =>
    match check_no_assign i s with
    | true =>
        do r <- compute_const_statement' s;
        let i1' := Integers.Int.intval i1 in
        let i2' := Integers.Int.intval i1 in
        Some (r * IZR (Z.max (i2' - i1' + 1)%Z 0)%Z)
    | false =>
        Some 0
    end
  | Sfor i e1 e2 s =>
    Some 0
  | Starget e => Some (compute_const_expr e)
  | Stilde e d el => None
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

Inductive match_cont: cont -> cont -> Prop :=
  | match_Kseq: forall s s' k k'
      (MCONT: match_cont k k')
      (TRS: transf_statement s = Some s'),
      match_cont (Kseq s k) (Kseq s' k')
  | match_Kstop:
      match_cont Kstop Kstop
  | match_Kfor: forall id e2 s s' k k'
      (MCONT: match_cont k k')
      (TRS: transf_statement s = Some s'),
      match_cont (Kfor id e2 s k) (Kfor id e2 s' k').

Inductive match_states: state -> state -> Prop :=
  | match_start_states: forall f s s' t k k' e m pm
      (MCONT: match_cont k k')
      (TRS: transf_statement s = Some s'),
      match_states (Start f s t k e m pm) (Start (transf_function f) s' t k' e m pm)
  | match_regular_states: forall f s s' t k k' e m pm
      (MCONT: match_cont k k')
      (TRS: transf_statement s = Some s'),
      match_states (State f s t k e m pm) (State (transf_function f) s' t k' e m pm)
  | match_return_states: forall f t e m pm,
      match_states (Return f t e m pm) (Return (transf_function f) t e m pm).

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step tge S1' t S2' /\ match_states S2 S2'.
Proof.
Abort.

Lemma transf_initial_states:
  forall S1, initial_state prog data params S1 ->
  exists S2, initial_state tprog data params S2 /\ match_states S1 S2.
Proof.
Abort.

Lemma transf_final_states:
  forall S1 S2 t r, match_states S1 S2 -> final_state t S1 r -> final_state t S2 r.
Proof.
Abort.

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
