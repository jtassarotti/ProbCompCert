From Coq Require Import Reals Psatz ssreflect Utf8.
Require Import Smallstep.
Require Import Errors.
Require Import Linking.

Require Import Stanlight.
Require Import Ssemantics.
Require Import Reparameterization.
Require Import DenotationalSimulationChange.
Require Import Coqlib.
Require Import Transforms.
Require Import IteratedRInt.

Local Open Scope string_scope.
Require Import Clightdefs.
Import Clightdefs.ClightNotations.

Local Open Scope clight_scope.

Inductive match_fundef (p: program) : fundef -> fundef -> Prop :=
  | match_fundef_internal: forall f tf parameters pmap correction,
      OK parameters = Errors.mmap (find_parameter p.(pr_defs)) p.(pr_parameters_vars) ->
      pmap = u_to_c_rewrite_map parameters ->
      correction = collect_corrections parameters ->
      transf_function pmap correction f = tf ->
      match_fundef p (Ctypes.Internal f) (Ctypes.Internal tf)
  | match_fundef_external: forall ef args res cc,
      match_fundef p (Ctypes.External ef args res cc) (Ctypes.External ef args res cc).

Definition match_varinfo (v: variable) (tv: variable) :=
  vd_type v = vd_type tv /\ vd_constraint tv = Cidentity.

Definition match_prog (p: program) (tp: program) : Prop :=
  exists parameters,
  List.Forall (fun '(id, _, ofun) => ofun = None) p.(pr_parameters_vars) /\
  OK parameters = Errors.mmap (find_parameter p.(pr_defs)) p.(pr_parameters_vars) /\
  match_program_gen match_fundef match_varinfo p p tp /\
  pr_parameters_vars tp = List.map (fun '(id, v, _) =>
                                 (id, vd_type v,
                                   Some (fun x => (unconstrained_to_constrained_fun (vd_constraint v) x))))
                            parameters.

Lemma program_of_program_eq p tp :
  pr_defs p = pr_defs tp -> (program_of_program p) = (program_of_program tp).
Proof.
  intros Heq. unfold program_of_program. rewrite Heq. eauto.
Qed.

Lemma transf_program_match:
  forall p tp: program, transf_program p = OK tp ->  match_prog p tp.
Proof.
  unfold transf_program, match_prog; intros p tp Htransf.
  eapply bind_inversion in Htransf as (?&Hcheck&Htransf).
  eapply bind_inversion in Htransf as (parameters&Heq&Htransf).
  eapply bind_inversion in Htransf as (tp'&Heq'&HOK).
  assert (program_of_program tp = tp') as ->.
  {
    unfold AST.transform_partial_program2 in Heq'.
    eapply bind_inversion in Heq' as (tp_defs'&Heq''&H').
    inversion H'. inversion HOK. subst. simpl. eauto.
  }
  eexists; split; eauto.
  { apply mmap_inversion in Hcheck.
    clear -Hcheck. induction Hcheck => //=.
    econstructor; eauto. destruct a1 as ((?&?)&[]); simpl in H; eauto; congruence. }
  split; eauto.
  split.
  {
    eapply match_transform_partial_program2; eauto.
    - intros. destruct f; inversion H; econstructor; eauto.
    - intros. inversion H. subst. econstructor; eauto.
  }
  inversion HOK; subst. simpl. eauto.
Qed.

Definition constrain_fn (c: constraint) : R -> R :=
  match c with
  | Cidentity => id
  | Clower_upper a b => constrain_lb_ub (IFR a) (IFR b)
  | Clower a => constrain_lb (IFR a)
  | Cupper a => constrain_ub (IFR a)
  end.

Definition unconstrain_fn (c: constraint) : R -> R :=
  match c with
  | Cidentity => id
  | Clower_upper a b => unconstrain_lb_ub (IFR a) (IFR b)
  | Clower a => unconstrain_lb (IFR a)
  | Cupper a => unconstrain_ub (IFR a)
  end.

Lemma constrain_unconstrain c x :
  in_interval x (constraint_to_interval c) ->
  constrain_fn c (unconstrain_fn c x) = x.
Proof.
  destruct c => //=; rewrite /in_interval/=; intros.
  - eapply constrain_lb_inv; intuition.
  - eapply constrain_ub_inv; intuition.
  - eapply constrain_lb_ub_inv; intuition.
Qed.

Lemma unconstrain_constrain c x :
  wf_interval (constraint_to_interval c) ->
  unconstrain_fn c (constrain_fn c x) = x.
Proof.
  intros Hwf.
  destruct c => //=; rewrite /in_interval/=; intros.
  - eapply unconstrain_lb_inv; intuition.
  - eapply unconstrain_ub_inv; intuition.
  - rewrite //=/wf_interval in Hwf. eapply unconstrain_lb_ub_inv. simpl in Hwf. nra.
Qed.

Section PRESERVATION.

Variable prog: Stanlight.program.
Variable tprog: Stanlight.program.
Variable TRANSL: match_prog prog tprog.

(* This is really round about and ugly, maybe I should have just made "parameters" an index of
   match_prog? But I don't know if that's compatible with the linker machinery *)
Definition found_parameters_aux :
  { x: list (AST.ident * variable * option (expr -> expr)) |
    (Errors.mmap (find_parameter prog.(pr_defs)) prog.(pr_parameters_vars)) = OK x}.
Proof.
  destruct (Errors.mmap (find_parameter prog.(pr_defs)) prog.(pr_parameters_vars)) as [l|] eqn:Heq.
  { exists l. eauto. }
  { abstract (exfalso; destruct TRANSL; intuition congruence). }
Qed.

Definition found_parameters := proj1_sig found_parameters_aux.

Lemma found_parameters_spec :
 Errors.mmap (find_parameter prog.(pr_defs)) prog.(pr_parameters_vars) = OK found_parameters.
Proof. unfold found_parameters. destruct found_parameters_aux; eauto. Qed.

Definition found_constraints :=
  map (fun '(id, var, f) =>  vd_constraint var) found_parameters.

Definition param_map (rs : list R) :=
  map (fun '(r, constraint) => constrain_fn constraint r) (combine rs (flatten_parameter_constraints prog)).

Definition param_unmap (rs : list R) :=
  map (fun '(r, constraint) => unconstrain_fn constraint r) (combine rs (flatten_parameter_constraints prog)).

Lemma param_map_unmap :
  ∀ x, in_list_rectangle x (parameter_list_rect prog) ->
       param_map (param_unmap x) = x.
Proof.
  rewrite /in_list_rectangle/parameter_list_rect/param_map/param_unmap.
  remember (flatten_parameter_constraints prog) as constraints eqn:Heq. clear Heq.
  intros x Hin.
  remember (map constraint_to_interval constraints) as intervals eqn:Heqn.
  revert constraints Heqn.
  induction Hin.
  - rewrite //=.
  - intros constraints Heqn. destruct constraints as [|c constraints]; first by (simpl in Heqn; congruence).
    simpl in Heqn. inversion Heqn; subst.
    rewrite /=. f_equal; eauto.
    apply constrain_unconstrain; auto.
Qed.

Lemma find_parameter_ident_match {A} l i' b (e' : A) i v e :
  find_parameter l (i', b, e') = OK (i, v, e) ->
  i' = i /\ e' = e.
Proof.
  induction l as [| (?&?) l] => //=.
  - destruct g; eauto.
    destruct (Pos.eq_dec _ _); subst; eauto.
    inversion 1; eauto.
Qed.

Lemma find_parameter_lookup_def_ident_gen (a : AST.ident * basic * option (expr -> expr)) i v e :
  find_parameter (pr_defs prog) a = OK (i, v, e) ->
  match List.find (fun '(id', v) => positive_eq_dec i id' && is_gvar v) (pr_defs prog) with
  | Some (_, AST.Gvar v') => (i, AST.gvar_info v') = (i, v)
  | _ =>  False
  end.
Proof.
  induction (pr_defs prog) as [| x l].
  - rewrite //=. destruct a as ((?&?)&?). inversion 1.
  - rewrite //=. destruct a as ((?&?)&?).
    destruct x as (id&def). destruct def.
    * rewrite andb_false_r; eauto.
    * destruct (Pos.eq_dec id i0).
      ** inversion 1; subst. rewrite //=. destruct (Pos.eq_dec i i) => /=; by eauto.
      ** intros Hfind.
         exploit (find_parameter_ident_match l i0 b o); eauto. intros (->&->). subst.
         destruct (Pos.eq_dec i id).
         { congruence. }
         rewrite //=. eapply IHl. eauto.
Qed.

Lemma find_parameter_lookup_def_ident_prog (a : AST.ident * basic * option (expr -> expr)) i v e :
  find_parameter (pr_defs prog) a = OK (i, v, e) ->
  lookup_def_ident prog i = (i, v).
Proof.
  intros Hfind%find_parameter_lookup_def_ident_gen.
  rewrite /lookup_def_ident. destruct (find (λ '(id', _), Pos.eq_dec i id' && _) (pr_defs _)) as [p|].
  * destruct p as (?&[]); intuition.
  * intuition.
Qed.

Lemma find_parameter_lookup_def_ident_tprog (a : AST.ident * basic * option (expr -> expr)) i b' e' v e :
  In (i, b', e') (pr_parameters_vars prog) ->
  find_parameter (pr_defs prog) a = OK (i, v, e) ->
  lookup_def_ident tprog i = (i, mkvariable (v.(vd_type)) Cidentity).
Proof.
  intros Hin Hfind. exploit find_parameter_lookup_def_ident_gen; eauto.
  rewrite /lookup_def_ident.
  intros Hlook.
  destruct TRANSL as (x&Hnone&HOK&Hmatch&?).
  destruct Hmatch as (Hforall2&?).
  edestruct (@list_find_fst_forall2 _ (AST.globdef fundef variable)
               ((fun '(id', v) => Pos.eq_dec i id' && is_gvar v))) as [Hleft|Hright]; first eauto.
  { intros ?? (?&?); auto. }
  { intros (?&?) (?&?). simpl. intros Hmatch. inversion Hmatch as [Hfst Hglob].
    simpl in Hfst, Hglob. inversion Hglob; subst => //=.
  }
  { simpl. destruct Hleft as (id'&g1&g2&Heq1&Heq2&Hident).
    rewrite Heq2. rewrite Heq1 in Hlook.
    inversion Hident as [Hfst_eq Hglob]. simpl in Hglob.
    inversion Hglob; auto.
    * subst; intuition.
    * subst. f_equal. inversion Hlook; subst.
      clear -H1.
      destruct H1. rewrite /=. destruct H as (H1&H2). rewrite H1. destruct i2. simpl in *. congruence.
  }
  destruct Hright as (Hnone1&Hnone2). rewrite Hnone1 in Hlook. intuition.
Qed.

Lemma map_repeat {A B} (f: A -> B) (a : A) (i : nat) :
  map f (repeat a i) = repeat (f a) i.
Proof.
  induction i => //=. congruence.
Qed.

Lemma flatten_parameter_variables_tprog:
  flatten_parameter_variables tprog = map (λ '(id, vd, f),
                                    (id, mkvariable (vd_type vd) Cidentity,
                                      Some (fun x => (unconstrained_to_constrained_fun (vd_constraint vd) x))))
                                    (flatten_parameter_variables prog).
Proof.
  rewrite /flatten_parameter_variables/flatten_ident_variable_list.
  rewrite concat_map.
  f_equal.
  rewrite ?map_map.
  destruct TRANSL as (x&Hnone&Heqx&Hmatch&Heq).
  rewrite Heq.
  clear Heq.
  revert x Heqx.
  remember (pr_parameters_vars prog) as prs eqn:Heqprs.
  assert (∀ x, In x prs -> In x (pr_parameters_vars prog)) as Hsub.
  { subst. eauto. }
  clear Heqprs Hnone.
  induction prs as [| a l].
  - intros x Heq. inversion Heq. subst. rewrite //=.
  - intros x Heqx.
    destruct x as [| a' x'].
    { symmetry in Heqx. inversion Heqx.
      apply bind_inversion in H0 as (((?&?)&?)&Hfind&Hbind).
      apply bind_inversion in Hbind as (?&Hfind'&Hbind').
      inversion Hbind'. }
    symmetry in Heqx. inversion Heqx.
    apply bind_inversion in H0 as (((?&?)&?)&Hfind&Hbind).
    apply bind_inversion in Hbind as (?&Hfind'&Hbind').
    inversion Hbind'; subst.
    rewrite //=.
    f_equal; last first.
    { eapply IHl; eauto. intros. intuition. }
    destruct a as ((?&?)&?).
    exploit (@find_parameter_ident_match (option (expr -> expr))); eauto. simpl. intros (?&?); subst.
    exploit (find_parameter_lookup_def_ident_prog); eauto. intros ->.
    exploit (find_parameter_lookup_def_ident_tprog); eauto.
    { eapply Hsub; eauto. left; eauto. }
    intros ->. rewrite /=.
    destruct (vd_type v) eqn:Hvdt; rewrite /=; rewrite ?Hvdt; eauto.
    rewrite map_repeat //=.
Qed.

Lemma flatten_parameter_constraints_tprog :
  flatten_parameter_constraints tprog =
    map (λ x, Cidentity) (flatten_parameter_constraints prog).
Proof.
  rewrite /flatten_parameter_constraints. rewrite flatten_parameter_variables_tprog.
  rewrite ?map_map.
  eapply map_ext. intros ((?&?)&?) => //.
Qed.

Lemma param_unmap_map :
  ∀ x, wf_rectangle_list (parameter_list_rect prog) ->
       in_list_rectangle x (parameter_list_rect tprog) ->
       param_unmap (param_map x) = x.
Proof.
  rewrite /in_list_rectangle/parameter_list_rect/param_map/param_unmap.
  rewrite flatten_parameter_constraints_tprog.
  remember (flatten_parameter_constraints prog) as constraints eqn:Heq. clear Heq.
  intros x Hwf Hin.
  remember (map constraint_to_interval (map (λ _, Cidentity) constraints)) as intervals eqn:Heqn.
  revert constraints Hwf Heqn.
  induction Hin.
  - rewrite //=.
  - intros constraints Hwf Heqn. destruct constraints as [|c constraints]; first by (simpl in Heqn; congruence).
    simpl in Heqn. inversion Heqn; subst.
    rewrite /=. f_equal; eauto.
    * apply unconstrain_constrain; auto.
      inversion Hwf; eauto.
    * eapply IHHin; eauto. inversion Hwf; eauto.
Qed.

Lemma dimen_preserved: parameter_dimension tprog = parameter_dimension prog.
Proof.
  rewrite /parameter_dimension flatten_parameter_constraints_tprog ?map_length //.
Qed.

Lemma wf_paramter_rect_tprog :
  wf_rectangle_list (parameter_list_rect prog) ->
  wf_rectangle_list (parameter_list_rect tprog).
Proof.
  clear 1.
  rewrite /parameter_list_rect flatten_parameter_constraints_tprog.
  induction (flatten_parameter_constraints prog).
  - rewrite //=.
  - simpl. econstructor; eauto. split; auto.
Qed.

Lemma param_unmap_in_dom :
  ∀ x, in_list_rectangle x (parameter_list_rect prog) ->
       in_list_rectangle (param_unmap x) (parameter_list_rect tprog).
Proof.
  rewrite /parameter_list_rect flatten_parameter_constraints_tprog.
  rewrite /param_unmap.
  induction (flatten_parameter_constraints prog).
  - intros x. inversion 1. subst. econstructor.
  - intros x. inversion 1; subst. simpl.
    econstructor.
    { split; auto => //=. }
    { eapply IHl. eauto. }
Qed.

Lemma param_map_in_dom :
  ∀ x,
    wf_rectangle_list (parameter_list_rect prog) ->
    in_list_rectangle x (parameter_list_rect tprog) ->
    in_list_rectangle (param_map x) (parameter_list_rect prog).
Proof.
  rewrite /parameter_list_rect flatten_parameter_constraints_tprog.
  rewrite /param_map.
  induction (flatten_parameter_constraints prog).
  - intros x Hwf. inversion 1. subst. econstructor.
  - intros x Hwf. inversion 1; subst. simpl.
    econstructor.
    { destruct a.
      * rewrite /=; split => //=.
      * rewrite /=; split => //=.
        apply constrain_lb_spec_strict.
      * rewrite /=; split => //=.
        apply constrain_ub_spec_strict.
      * simpl in Hwf. inversion Hwf.
        rewrite /=; split => //=; apply constrain_lb_ub_spec_strict; auto.
    }
    eapply IHl; eauto.
    inversion Hwf; eauto.
Qed.

(*
Lemma external_funct_preserved:
  match_external_funct (globalenv prog) (globalenv tprog).

Lemma global_env_equiv :
  Senv.equiv (globalenv prog) (globalenv tprog).
*)

Lemma Forall_repeat {A: Type} (a : A) (n: nat) (P : A -> Prop) :
  P a -> Forall P (repeat a n).
Proof.
  intros. induction n; econstructor; eauto.
Qed.

Lemma flatten_parameter_variables_out_none :
  List.Forall (fun '(id, _, ofun) => ofun = None) (flatten_parameter_variables prog).
Proof.
  rewrite /flatten_parameter_variables. rewrite /flatten_ident_variable_list.
  destruct TRANSL as (?&Hnone&_).
  induction (pr_parameters_vars).
  { rewrite //=. }
  { rewrite //=. apply Forall_app; split; last first.
    { eapply IHl. inversion Hnone; eauto. }
    { destruct a as ((?&?)&?) => /=.
      inversion Hnone; subst.
      destruct (lookup_def_ident prog i) as (?&?).
      destruct (vd_type _); try (econstructor; eauto; done).
      apply Forall_repeat; eauto.
    }
  }
Qed.

Definition exp_ef_external :=
  (AST.EF_external "exp" (AST.mksignature (AST.Tfloat :: nil) (AST.Tret AST.Tfloat)
                            (AST.mkcallconv None false false))).

Axiom global_env_exp :
  exists loc,
  Globalenvs.Genv.find_symbol (globalenv tprog) ($"exp") = Some loc /\
  Globalenvs.Genv.find_funct (globalenv tprog) (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            exp_ef_external
            (Ctypes.Tcons tdouble Ctypes.Tnil)
            tdouble
            (AST.mkcallconv None false false)).

Axiom exp_ext_spec v :
  forall a ge m,
  Events.external_call exp_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m Events.E0 (Values.Vfloat (IRF (exp a))) m.

Axiom IFR_IRF_inv :
  ∀ x, IFR (IRF x) = x.
Axiom IRF_IFR_inv :
  ∀ x, IRF (IFR x) = x.

Axiom float_add_irf: forall a b,
  (Floats.Float.add (IRF a) (IRF b)) = IRF (a + b).
Axiom float_sub_irf: forall a b,
  (Floats.Float.sub (IRF a) (IRF b)) = IRF (a - b).

Lemma param_unmap_out_inv :
  ∀ d p, is_safe prog d (map R2val p) ->
                 eval_param_map_list prog p = eval_param_map_list tprog (param_unmap p).
Proof.
  rewrite /eval_param_map_list.
  intros d p _.
  rewrite /flatten_parameter_out.
  rewrite /param_unmap.
  rewrite flatten_parameter_variables_tprog.
  rewrite /flatten_parameter_constraints.
  specialize (flatten_parameter_variables_out_none) => Hnone.
  remember (flatten_parameter_variables prog) as pvars eqn:Heq. clear Heq.
  revert pvars Hnone.
  induction p => pvars Hnone.
  { rewrite /eval_param_map_list /=//. }
  destruct pvars => //=.
  f_equal.
  { f_equal.
    destruct p0 as ((?&?)&?). inversion Hnone; subst.
    rewrite /=.
    transitivity (Values.Vfloat (IRF a)).
    { apply eval_expr_fun_spec. econstructor. }
    symmetry.

    destruct (vd_constraint).
    { apply eval_expr_fun_spec; econstructor. }
    { apply eval_expr_fun_spec. rewrite /unconstrained_to_constrained_fun.
      edestruct (global_env_exp) as (expl&?&?).
      simpl.
      econstructor.
      { econstructor.
        econstructor.
        eapply eval_Evar_global; eauto.
        { eapply deref_loc_reference; eauto. }
        { repeat econstructor. }
        { eauto. }
        2:{  eauto. }
        rewrite /exp_ef_external; reflexivity.
        eapply exp_ext_spec.
      }
      { econstructor. }

      simpl.
      rewrite /unconstrain_lb.
      rewrite exp_ln.
      2: { admit. }

      rewrite /Cop.sem_add//=.
      rewrite /Cop.sem_binarith//=.

      replace f with (IRF (IFR f)) at 2 by (apply IRF_IFR_inv).
      do 2 f_equal.
      rewrite float_add_irf. f_equal. nra.
    }
    { apply eval_expr_fun_spec. rewrite /unconstrained_to_constrained_fun.
      edestruct (global_env_exp) as (expl&?&?).
      simpl.
      econstructor.
      { econstructor. }
      {
        econstructor.
        econstructor.
        eapply eval_Evar_global; eauto.
        { eapply deref_loc_reference; eauto. }
        { repeat econstructor. }
        { eauto. }
        2:{  eauto. }
        rewrite /exp_ef_external; reflexivity.
        eapply exp_ext_spec.
      }
      simpl.
      rewrite /Cop.sem_sub//=.
      rewrite /Cop.sem_binarith//=.
      rewrite /unconstrain_ub.
      rewrite exp_Ropp.
      rewrite exp_ln.
      2: { admit. }
      do 2 f_equal.
      replace f with (IRF (IFR f)) at 1 by (apply IRF_IFR_inv).
      do 2 f_equal.
      rewrite float_sub_irf. f_equal.
      admit.
      (* TODO: we switched to using a monotone transform, so have to change code emitted as well *)
    }
    { admit. }
  }
  eapply IHp; eauto. inversion Hnone; eauto.
Abort.

Variable data : list Values.val.
Variable params : list Values.val.

(* TODO: Joe: this doesn't make sense, because we ought to be remapping data/params in target *)
Theorem transf_program_correct tval:
  forward_simulation (Ssemantics.semantics prog data params tval) (Ssemantics.semantics tprog data params tval).
Proof.
Admitted.

End PRESERVATION.

Global Instance TransfReparameterizationtLink : TransfLink match_prog.
Admitted.
