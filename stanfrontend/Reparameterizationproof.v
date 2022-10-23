From Coq Require Import Reals Psatz ssreflect Utf8.
Require Import Smallstep.
Require Import Errors.
Require Import Linking.
Require Import Globalenvs.

Require Import Stanlight.
Require Import Ssemantics.
Require Import Reparameterization.
Require Import DenotationalSimulationChange.
Require Import Coqlib.
Require Import Transforms.
Require Import IteratedRInt.
Require Import Memory.
Require Import ParamMap.
Require Import StanEnv.

Local Open Scope string_scope.
Require Import Clightdefs.
Import Clightdefs.ClightNotations.

Local Open Scope clight_scope.

Require Import RealsExt.
Import Continuity.


(* TODO: it seems to have been annoying to have defined this this way,
   probably would have been better to make parameters be a parameter rather than existentially quantifying? *)
Inductive match_fundef (p: program) : fundef -> fundef -> Prop :=
  | match_fundef_internal: forall f tf parameters pmap correction,
      OK parameters = Errors.mmap (find_parameter p.(pr_defs)) p.(pr_parameters_vars) ->
      pmap = u_to_c_rewrite_map parameters ->
      correction = collect_corrections parameters ->
      transf_function pmap correction f = OK tf ->
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
                            parameters /\
  Forall (λ '(id, _, _), ¬ In id math_idents) (pr_parameters_vars p).

Lemma param_check_shadow_ok id b o xt:
  param_check_shadow (id, b, o) = OK xt ->
  ¬ In id math_idents.
Proof.
  intros Hin.
  unfold param_check_shadow in Hin.
  destruct (forallb _ _) eqn:Hforallb; last by inv Hin.
  rewrite forallb_forall in Hforallb * => Hforallb.
  intros Hin'. eapply Hforallb in Hin'.
  destruct (Pos.eq_dec id id); inv Hin'.
  congruence.
Qed.

Lemma program_of_program_eq p tp :
  pr_defs p = pr_defs tp -> (program_of_program p) = (program_of_program tp).
Proof.
  intros Heq. unfold program_of_program. rewrite Heq. eauto.
Qed.

Lemma transf_program_match:
  forall p tp: program, transf_program p = OK tp -> match_prog p tp.
Proof.
  unfold transf_program, match_prog; intros p tp Htransf.
  eapply bind_inversion in Htransf as (?&Hcheck&Htransf).
  eapply bind_inversion in Htransf as (?&Hcheck'&Htransf).
  eapply bind_inversion in Htransf as (?&?&Htransf).
  eapply bind_inversion in Htransf as (?&?&Htransf).
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
    - intros. destruct f; inversion H.
      { monadInv H1.  inv EQ; subst; eauto.
         econstructor; eauto. }
      { monadInv H1. econstructor. }
    - intros. inversion H1. subst. econstructor; eauto.
  }
  split.
  { inversion HOK; subst. simpl. eauto. }
  apply mmap_inversion in Hcheck'.
  apply Forall_forall. intros ((?&?)&?) Hin.
  eapply list_forall2_in_left in Hcheck' as (?&Hin'&Hcheck'); eauto.
  eapply param_check_shadow_ok; eauto.
Qed.

Definition constrain_fn (c: constraint) : R -> R :=
  match c with
  | Cidentity => id
  | Clower_upper a b => constrain_lb_ub (IFR a) (IFR b)
  | Clower a => constrain_lb (IFR a)
  | Cupper a => constrain_ub (IFR a)
  end.

Definition log_deriv_constrain_fn (c: constraint) x : R :=
  match c with
  | Cidentity => 0
  | Clower_upper a b => ln (deriv_constrain_lb_ub (IFR a) (IFR b) x)
  | Clower a => ln (deriv_constrain_lb (IFR a) x)
  | Cupper a => ln (deriv_constrain_ub (IFR a) x)
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

Variable prog_genv_has_mathlib :
  genv_has_mathlib (globalenv prog).

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

Definition gs :=
  map (constrain_fn) (flatten_parameter_constraints prog).

Definition log_dgs :=
  map (log_deriv_constrain_fn) (flatten_parameter_constraints prog).

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
  i' = i /\ e' = e /\ b = vd_type v.
Proof.
  induction l as [| (?&?) l] => //=.
  - destruct g; eauto.
    destruct (Pos.eq_dec _ _); subst; eauto.
    destruct (valid_equiv_param_type _ _) eqn:Heq; inversion 1.
    exploit valid_equiv_param_type_spec; eauto.
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
      ** destruct (valid_equiv_param_type _ _); inversion 1; subst.
         rewrite //=. destruct (Pos.eq_dec i i) => /=; by eauto.
      ** intros Hfind.
         exploit (find_parameter_ident_match l i0 b o); eauto. intros (->&->&?). subst.
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

Lemma pr_parameters_vars_found_parameters :
  pr_parameters_vars prog = map (λ '(id, v, fe), (id, vd_type v, fe)) found_parameters.
Proof.
  specialize (found_parameters_spec) => Hmmap.
  remember (pr_parameters_vars prog) as prs eqn:Heqprs.
  assert (∀ x, In x prs -> In x (pr_parameters_vars prog)) as Hsub.
  { subst. eauto. }
  clear Heqprs.
  revert Hmmap. generalize found_parameters.
  induction prs.
  - rewrite //=. intros fps. inversion 1 => //=.
  - destruct a as ((?&?)&?). intros fps Hmmap.
    simpl in Hmmap. monadInv Hmmap.
    destruct x as ((?&?)&?).
    simpl. f_equal; eauto; last first.
    { eapply IHprs; eauto. intros. apply Hsub. by right. }
    exploit (@find_parameter_ident_match (option (expr -> expr))); eauto. intros (?&?&?); subst.
    auto.
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
  destruct TRANSL as (x&Hnone&Heqx&Hmatch&Heq&_).
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

Lemma parameters_ids_preserved :
  pr_parameters_ids tprog = pr_parameters_ids prog.
Proof.
  unfold pr_parameters_ids.
  destruct TRANSL as (x&Hnone&Heqx&Hmatch&Heq&_).
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
    auto.
Qed.

Lemma flatten_parameter_constraints_tprog :
  flatten_parameter_constraints tprog =
    map (λ x, Cidentity) (flatten_parameter_constraints prog).
Proof.
  rewrite /flatten_parameter_constraints. rewrite flatten_parameter_variables_tprog.
  rewrite ?map_map.
  eapply map_ext. intros ((?&?)&?) => //.
Qed.

Lemma flatten_parameter_list_tprog :
  (flatten_parameter_list tprog.(pr_parameters_vars)) =
    (flatten_parameter_list prog.(pr_parameters_vars)).
Proof.
  rewrite /flatten_parameter_list. f_equal.
  destruct TRANSL as (x&Hnone&Heqx&Hmatch&Heq&_).
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
    exploit (@find_parameter_ident_match (option (expr -> expr))); eauto. simpl. intros (?&?&?); subst.
    eauto.
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

Lemma param_map_gs :
  ∀ x, in_list_rectangle x (parameter_list_rect tprog) ->
       list_apply gs x = param_map x.
Proof.
  rewrite /param_map/gs/list_apply//=.
  intros x. clear 1. revert x.
  induction (flatten_parameter_constraints prog) as [| c l]; intros x.
  { rewrite //=. destruct x => //=. }
  { destruct x => //=. f_equal; auto. }
Qed.

Definition target_map (d p : list Values.val) x := list_plus (list_apply log_dgs (map val2R p)) + x.
Definition target_unmap (d p : list Values.val) x := x - list_plus (list_apply log_dgs (map val2R p)).

Lemma target_map_unmap : ∀ d p x, target_map d p (target_unmap d p x) = x.
Proof. intros d p x. rewrite /target_map/target_unmap. field. Qed.

Lemma target_map_dgs :
  ∀ data x, in_list_rectangle x (parameter_list_rect tprog) ->
  target_map data (map R2val x) (log_density_of_program prog data (map R2val (param_map x))) =
    list_plus (list_apply log_dgs x) + log_density_of_program prog data (map R2val (param_map x)).
Proof.
  rewrite /target_map. intros. f_equal. f_equal. f_equal.
  rewrite map_map. etransitivity; last eapply map_id.
  eapply map_ext. intros. rewrite //= IFR_IRF_inv //.
Qed.

Lemma gs_monotone :
  wf_rectangle_list (parameter_list_rect prog) ->
  Forall2 strict_monotone_on_interval (parameter_list_rect tprog) gs.
Proof.
  rewrite /gs/parameter_list_rect.
  intros Hwf.
  rewrite flatten_parameter_constraints_tprog.
  induction (flatten_parameter_constraints prog) as [| c l].
  { econstructor. }
  {  simpl. econstructor; last first.
     { eapply IHl. inversion Hwf; eauto. }
     rewrite /strict_monotone_on_interval. intros x y (_&Hlt&_).
     destruct c.
     - rewrite //=.
     - apply constrain_lb_strict_increasing. auto.
     - apply constrain_ub_strict_increasing. auto.
     - apply constrain_lb_ub_strict_increasing; auto.
       inversion Hwf. subst. eauto.
  }
Qed.

Lemma gs_image :
  wf_rectangle_list (parameter_list_rect prog) ->
  Forall3 is_interval_image gs (parameter_list_rect tprog) (parameter_list_rect prog).
Proof.
  rewrite /gs/parameter_list_rect.
  intros Hwf.
  rewrite flatten_parameter_constraints_tprog.
  induction (flatten_parameter_constraints prog) as [| c l].
  { econstructor. }
  {  simpl. econstructor; last first.
     { eapply IHl. inversion Hwf; eauto. }
     rewrite /is_interval_image/=.
     destruct c.
     - split; auto.
       split.
       { simpl. apply is_lim_right_lim; first congruence. apply is_lim_id. }
       { simpl. apply is_lim_left_lim; first congruence. apply is_lim_id. }
     - split; auto.
       { simpl. intros. split; auto. apply constrain_lb_spec_strict. }
       split.
       { apply constrain_lb_lim_right_correct; congruence. }
       { apply constrain_lb_lim_left_correct; congruence. }
     - split; auto.
       { simpl. intros. split; auto. apply constrain_ub_spec_strict. }
       split.
       { apply constrain_ub_lim_right_correct; congruence. }
       { apply constrain_ub_lim_left_correct; congruence. }
     - split; auto.
       { simpl. intros; apply constrain_lb_ub_spec_strict; inversion Hwf; auto. }
       split.
       { apply constrain_lb_ub_lim_right_correct; congruence. }
       { apply constrain_lb_ub_lim_left_correct; congruence. }
  }
Qed.

Lemma gs_deriv :
  wf_rectangle_list (parameter_list_rect prog) ->
  Forall3 continuous_derive_on_interval (parameter_list_rect tprog) gs
    (map (λ (f : R → R) (x : R), exp (f x)) log_dgs).
Proof.
  rewrite /log_dgs/gs/parameter_list_rect.
  intros Hwf.
  rewrite flatten_parameter_constraints_tprog.
  induction (flatten_parameter_constraints prog) as [| c l].
  { econstructor. }
  {  simpl. econstructor; last first.
     { eapply IHl. inversion Hwf; eauto. }
     rewrite /continuous_derive_on_interval. intros x (Hlt1&Hlt2).
     destruct c.
     - rewrite //=. split.
       { rewrite exp_0. apply: Derive.is_derive_id. }
       { apply continuous_const. }
     - split.
       { rewrite /=. rewrite exp_ln; last apply deriv_constrain_lb_pos.
         apply deriv_constrain_lb_correct. }
       rewrite /=.
       eapply continuous_ext.
       { intros ?. rewrite exp_ln; last apply deriv_constrain_lb_pos. reflexivity. }
       { eapply deriv_constrain_lb_continuous. }
     - split.
       { rewrite /=. rewrite exp_ln; last apply deriv_constrain_ub_pos.
         apply deriv_constrain_ub_correct. }
       rewrite /=.
       eapply continuous_ext.
       { intros ?. rewrite exp_ln; last apply deriv_constrain_ub_pos. reflexivity. }
       { eapply deriv_constrain_ub_continuous. }
     - split.
       { rewrite /=. rewrite exp_ln; last apply deriv_constrain_lb_ub_pos.
         apply deriv_constrain_lb_ub_correct. inversion Hwf; eauto. }
       rewrite /=.
       eapply continuous_ext.
       { intros ?. inversion Hwf. rewrite exp_ln; last apply deriv_constrain_lb_ub_pos; auto. }
       { eapply deriv_constrain_lb_ub_continuous. }
  }
Qed.

Definition fpmap := u_to_c_rewrite_map found_parameters.
Definition fcorrection := collect_corrections found_parameters.

Inductive match_fundef' (p: program) : fundef -> fundef -> Prop :=
  | match_fundef_internal': forall f tf ,
      transf_function fpmap fcorrection f = OK tf ->
      match_fundef' p (Ctypes.Internal f) (Ctypes.Internal tf)
  | match_fundef_external': forall ef args res cc,
      match_fundef' p (Ctypes.External ef args res cc) (Ctypes.External ef args res cc).

Definition match_prog' : Prop :=
  match_program_gen match_fundef' match_varinfo prog prog tprog /\
  pr_parameters_vars tprog = List.map (fun '(id, v, _) =>
                                 (id, vd_type v,
                                   Some (fun x => (unconstrained_to_constrained_fun (vd_constraint v) x))))
                               found_parameters /\
  Forall (λ '(id, _, _), ¬ In id math_idents) (pr_parameters_vars prog).

Lemma match_fundef_fundef' f tf :
  match_fundef prog f tf ->
  match_fundef' prog f tf.
Proof.
  inversion 1.
  - subst. assert (parameters = found_parameters) as ->.
    { specialize (found_parameters_spec) => Heq. congruence. }
    econstructor; eauto.
  - subst. econstructor; eauto.
Qed.

Lemma TRANSL' : match_prog'.
Proof.
  destruct TRANSL as (params'&?&?&?&?&Hcheck).
  subst. assert (params' = found_parameters) as ->.
  { specialize (found_parameters_spec) => Heq. congruence. }
  split; last by eauto.
  inversion H1.
  split; eauto.

  clear -H3. induction H3.
  { econstructor. }
  { econstructor; last by eauto.
    inversion H; econstructor; eauto.
    inversion H1; subst; econstructor; eauto.
    inversion H5. subst.
    eapply match_fundef_fundef'.
    eauto.
  }
Qed.

Let ge := globalenv prog.
Let tge := globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  ∃ f', Genv.find_funct tge v = Some f' /\ transf_fundef fpmap fcorrection f = OK f'.
Proof.
  intros. destruct TRANSL' as (Hmatch&Hrest&Hcheck).
  eapply (Genv.find_funct_match) in Hmatch as (?&tfun&Htfun); eauto.
  intuition.
  eexists; split; eauto.
  inversion H2; eauto.
  rewrite /=. subst. rewrite H1 => //=.
Qed.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  ∃ f', Genv.find_funct_ptr tge v = Some f' /\ transf_fundef fpmap fcorrection f = OK f'.
Proof.
  intros. destruct TRANSL' as (Hmatch&Hrest&Hcheck).
  eapply (Genv.find_funct_ptr_match) in Hmatch as (?&tfun&Htfun); eauto.
  intuition.
  eexists; split; eauto.
  inversion H2; eauto.
  rewrite /=. subst. rewrite H1 => //=.
Qed.

Lemma ext_functions_preserved:
  forall v ef tyargs tyret cconv,
  Genv.find_funct ge v = Some (Ctypes.External ef tyargs tyret cconv) ->
  Genv.find_funct tge v = Some (Ctypes.External ef tyargs tyret cconv).
Proof.
  intros.
  exploit (functions_translated); eauto. intros (f'&Hfind&Htrans).
  inv Htrans. auto.
Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. destruct TRANSL'.
  eapply Genv.find_symbol_match; intuition eauto.
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  intros. destruct TRANSL'.
  eapply Genv.senv_match; eauto.
Qed.

Lemma tprog_genv_has_mathlib :
  genv_has_mathlib (globalenv tprog).
Proof.
  move: prog_genv_has_mathlib.
  rewrite /genv_has_mathlib.
  rewrite /genv_exp_spec/genv_log_spec/genv_expit_spec.
  rewrite ?symbols_preserved.
  intros (Hexp&Hexpit&Hlog).
  intuition.
  { destruct Hexp as (loc&?). exists loc. erewrite ext_functions_preserved; intuition eauto. }
  { destruct Hexpit as (loc&?). exists loc. erewrite ext_functions_preserved; intuition eauto. }
  { destruct Hlog as (loc&?). exists loc. erewrite ext_functions_preserved; intuition eauto. }
Qed.

Lemma eval_expr_fun_const pr v :
  eval_expr_fun pr (Econst_float v Breal) = (Values.Vfloat v).
Proof.
  apply eval_expr_fun_spec. econstructor.
Qed.

Lemma eval_constrained_fun r c env m pm t :
  env_no_shadow_mathlib env ->
  param_mem_no_shadow_mathlib pm ->
  eval_expr (globalenv tprog) env m pm t
    (unconstrained_to_constrained_fun c
       (Econst_float (IRF r) Breal)) (Values.Vfloat (IRF (constrain_fn c r))).
Proof.
  intros Hnoshadow1 Hnoshadow2.
    destruct c.
    { econstructor. }
    { rewrite /unconstrained_to_constrained_fun.
      edestruct (tprog_genv_has_mathlib) as ((expl&?&?)&_).
      simpl.
      econstructor.
      { econstructor.
        eapply eval_Elvalue.
        eapply eval_Evar_global; eauto.
        { rewrite /env_no_shadow_mathlib in Hnoshadow1.
          inversion Hnoshadow1 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          eauto.
        }
        {
          inversion Hnoshadow2 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          eauto.
        }
        { eapply deref_loc_reference; eauto. }
        { repeat econstructor. }
        { eauto. }
        2:{  eauto. }
        rewrite /exp_ef_external; reflexivity.
        eapply exp_ext_spec.
      }
      { econstructor. }

      simpl.
      rewrite /Sop.sem_add//=.
      rewrite /Sop.sem_binarith//=.
      rewrite /constrain_lb.
      rewrite -float_add_irf. repeat f_equal. rewrite IRF_IFR_inv //.
    }
    {
      rewrite /unconstrained_to_constrained_fun.
      edestruct (tprog_genv_has_mathlib) as ((expl&?&?)&_).
      simpl.
      econstructor.
      { econstructor. }
      {
        assert ((Floats.Float.sub Floats.Float.zero (IRF r))
               = (IRF (- r))) as Heq.
        { rewrite -(IRF_IFR_inv (Floats.Float.zero)).
          rewrite float_sub_irf. f_equal. rewrite IFR_zero. nra.
        }
        econstructor.
        eapply eval_Elvalue.
        eapply eval_Evar_global; eauto.
        { rewrite /env_no_shadow_mathlib in Hnoshadow1.
          inversion Hnoshadow1 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          eauto.
        }
        {
          inversion Hnoshadow2 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          eauto.
        }
        { eapply deref_loc_reference; eauto. }
        { repeat econstructor. }
        { eauto. }
        2:{  eauto. }
        rewrite /exp_ef_external; reflexivity.
        rewrite ?Heq; eapply exp_ext_spec.
      }
      simpl.
      rewrite /Sop.sem_sub//=.
      rewrite /Sop.sem_binarith//=.
      replace f with (IRF (IFR f)) at 1 by (apply IRF_IFR_inv).
      rewrite float_sub_irf. f_equal.
    }
    {
      rewrite /unconstrained_to_constrained_fun.
      edestruct (tprog_genv_has_mathlib) as (?&(expl&?&?)&_).
      simpl.
      econstructor.
      { econstructor. }
      econstructor.
      { repeat econstructor. }
      {
        econstructor.
        eapply eval_Elvalue.
        eapply eval_Evar_global; eauto.
        { rewrite /env_no_shadow_mathlib in Hnoshadow1.
          inversion Hnoshadow1 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          eauto.
        }
        {
          inversion Hnoshadow2 as [|??? Hnoshadow'].
          inversion Hnoshadow' as [|??? Hnoshadow''].
          inversion Hnoshadow'' as [|??? Hnoshadow'''].
          eauto.
        }
        { eapply deref_loc_reference; eauto. }
        { repeat econstructor. }
        { eauto. }
        2:{  eauto. }
        rewrite /expit_ef_external; reflexivity.
        eapply expit_ext_spec.
      }
      simpl.
      rewrite //=.
      rewrite /Sop.sem_binarith//=.
      rewrite /Sop.sem_add//=.
      rewrite /Sop.sem_binarith//=.
      do 2 f_equal.
      rewrite /constrain_lb_ub.
      rewrite float_add_irf'; repeat f_equal.
      rewrite float_mul_irf'.
      rewrite float_sub_irf'.
      rewrite ?IFR_IRF_inv.
      f_equal.
    }
Qed.

Lemma eval_constrained_fun' r c env m pm t :
  in_interval r (constraint_to_interval c) ->
  env_no_shadow_mathlib env ->
  param_mem_no_shadow_mathlib pm ->
  eval_expr (globalenv tprog) env m pm t
    (unconstrained_to_constrained_fun c
       (Econst_float (IRF (unconstrain_fn c r)) Breal)) (Values.Vfloat (IRF r)).
Proof.
  intros.
  assert (r = constrain_fn c (unconstrain_fn c r)) as Heq.
  { rewrite constrain_unconstrain //. }
  rewrite {2}Heq.
  eapply eval_constrained_fun; auto.
Qed.

Lemma eval_param_map_list_preserved :
  ∀ x,
    in_list_rectangle x (parameter_list_rect tprog) ->
    eval_param_map_list tprog x = eval_param_map_list prog (param_map x).
Proof.
  rewrite /eval_param_map_list/parameter_list_rect.
  intros x.
  rewrite /flatten_parameter_out.
  rewrite /param_map.
  rewrite /flatten_parameter_constraints.
  rewrite flatten_parameter_variables_tprog.
  specialize (flatten_parameter_variables_out_none) => Hnone.
  remember (flatten_parameter_variables prog) as pvars eqn:Heq. clear Heq.
  revert pvars Hnone.
  induction x => pvars Hnone Hin.
  { rewrite /eval_param_map_list /=//. }
  destruct pvars => //=.
  f_equal.
  { f_equal.
    destruct p as ((?&?)&?). inversion Hnone; subst. rewrite eval_expr_fun_const /=.
    apply eval_expr_fun_spec.
    apply eval_constrained_fun.
    { repeat (econstructor; first by eauto using Maps.PTree.gempty). econstructor. }
    { repeat (econstructor; first by eauto using gempty). econstructor. }
  }
  eapply IHx; eauto.
  { inversion Hnone; eauto. }
  { inversion Hin; subst. eauto. }
Qed.

Variable data : list Values.val.
Variable params : list R.

Scheme eval_expr_rec := Minimality for eval_expr Sort Prop
  with eval_lvalue_rec := Minimality for eval_lvalue Sort Prop
  with eval_exprlist_rec := Minimality for eval_exprlist Sort Prop.

Combined Scheme eval_expr_mutind from eval_expr_rec, eval_lvalue_rec, eval_exprlist_rec.

Lemma typeof_fpmap :
  ∀ i fe efill, fpmap i = Some fe -> typeof efill = Breal -> typeof (fe efill) = Breal.
Proof.
  rewrite /fpmap.
  induction found_parameters as [| ((?&?)&?)] => //=.
  intros i' fe efill.
  destruct (Pos.eq_dec _ _).
  { rewrite /unconstrained_to_constrained.
    inversion 1. subst. intros Hefill.
    destruct (vd_constraint _) => //=.
  }
  intros. eauto.
Qed.

Lemma typeof_transf_expr a a' :
  transf_expr fpmap a = OK a' ->
  typeof a' = typeof a.
Proof.
  induction a => //=; intros HEQ; try monadInv HEQ; subst => //=.
  { destruct (fpmap i) as [fe|] eqn:Hfe => //=; try (by inversion HEQ).
    destruct b; inversion HEQ => //=.
    eapply typeof_fpmap; eauto. }
  { destruct a => //=; try monadInv EQ0; subst => //=.
    destruct (fpmap i) as [fe|] eqn:Hfe => //=; try (by inversion HEQ);
    destruct b; inversion EQ0 => //=.
    eapply typeof_fpmap; eauto. }
Qed.

Definition match_param_mem_some (pm0 pm1 : param_mem) :=
  ∀ id ofs fl, ParamMap.get pm0 id ofs = Some fl ->
              ∃ fe fl', ParamMap.get pm1 id ofs = Some fl' /\
                       fpmap id = Some fe /\
                          (∀ en' m' t',
                              env_no_shadow_mathlib en' ->
                              eval_expr tge en' m' pm1 t'
                                (fe (Econst_float fl' Breal)) (Values.Vfloat fl)).

Definition match_param_mem_none (pm0 pm1 : param_mem) :=
  ∀ id, ParamMap.is_id_alloc pm0 id = false -> ParamMap.is_id_alloc pm1 id = false.

Definition match_param_mem pm0 pm1 :=
  match_param_mem_some pm0 pm1 /\ match_param_mem_none pm0 pm1.

Definition wf_param_mem pm :=
  (∀ id, ParamMap.is_id_alloc pm id = false -> fpmap id = None).

Definition valid_env (en : env) :=
  forall id, Maps.PTree.get id en <> None -> fpmap id = None.

Definition env_no_shadow_param (en : env) pm :=
  forall id, ParamMap.is_id_alloc pm id = true -> Maps.PTree.get id en = None.

Lemma found_parameters_irrel {A B} id b1 (oe1 : A) b2 (oe2 : B) id1' v1 oe1' id2' v2 oe2' :
  find_parameter (pr_defs prog) (id, b1, oe1) = OK (id1', v1, oe1') ->
  find_parameter (pr_defs prog) (id, b2, oe2) = OK (id2', v2, oe2') ->
  id1' = id2' /\ v1 = v2.
Proof.
  induction (pr_defs prog).
  - rewrite //=.
  - rewrite //=. destruct a as (?&?).
    destruct g.
    { eauto. }
    destruct (Pos.eq_dec i id); subst.
    { destruct (valid_equiv_param_type _ _); last by inversion 1.
      destruct (valid_equiv_param_type _ _); last by inversion 1.
      intros Heq1 Heq2. inv Heq1. inv Heq2. eauto.
    }
    eauto.
Qed.

Lemma In_found_parameters_inv id v oe :
  In (id, v, oe) found_parameters ->
  find_parameter (pr_defs prog) (id, vd_type v, oe) = OK (id, v, oe).
Proof.
  specialize (found_parameters_spec).
  intros Hforall2%mmap_inversion.
  intros HIn.
  eapply list_forall2_in_right in Hforall2; eauto.
  destruct Hforall2 as (((?&?)&?)&Hin&Heq).
  exploit (find_parameter_ident_match (pr_defs prog) i b o); eauto.
  intuition congruence.
Qed.

Lemma found_parameters_dup id v1 v2 oe1 oe2 :
  In (id, v1, oe1) found_parameters ->
  In (id, v2, oe2) found_parameters ->
  v1 = v2.
Proof.
  intros Hin1 Hin2.
  exploit In_found_parameters_inv; first eapply Hin1.
  exploit In_found_parameters_inv; first eapply Hin2.
  intros Hfind1 Hfind2.
  exploit (found_parameters_irrel id (vd_type v1) oe1 (vd_type v2) oe2); eauto.
  intuition.
Qed.

Lemma fpmap_spec id v oe :
  In (id, v, oe) found_parameters ->
  fpmap id = Some (unconstrained_to_constrained_fun (vd_constraint v)).
Proof.
  rewrite /fpmap. specialize (found_parameters_dup).
  induction (found_parameters) as [|((?&?)&?) l IH] => Hin_spec.
  - inversion 1.
  - simpl. intros [Heq|Hin].
    { inv Heq. destruct (Pos.eq_dec _ _); try congruence. rewrite /unconstrained_to_constrained//. }
    {
      destruct (Pos.eq_dec _ _).
      { subst. exploit Hin_spec.
        { left. eauto. }
        { right. eauto. }
        intros ->. rewrite //=.
      }
      eapply IH; eauto. intros. eapply Hin_spec; by right; eauto.
    }
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

Lemma assign_global_params_is_id_alloc_in_flat1 flat_ids pm1 vs pm2 :
  assign_global_params flat_ids pm1 vs pm2 ->
  ∀ id, ParamMap.is_id_alloc pm2 id  = true ->
               (ParamMap.is_id_alloc pm1 id = true) ∨
               (∃ b ofs', In (id, b, ofs') flat_ids).
Proof.
  induction 1.
  - intuition.
  - intros id' Halloc.
    edestruct IHassign_global_params as [Hleft|Hright]; eauto.
    { subst.
      destruct (Pos.eq_dec id id'); subst.
      { right. do 2 eexists; by left; eauto. }
      { rewrite is_id_set_other in Hleft; eauto. }
    }
    right. clear -Hright. destruct Hright as (?&?&?).
    do 2 eexists; eauto. right. eauto.
Qed.

Lemma assign_global_params_some_in_flat1 flat_ids pm1 vs pm2 :
  assign_global_params flat_ids pm1 vs pm2 ->
  ∀ id ofs fl, ParamMap.get pm2 id ofs = Some fl ->
               (ParamMap.get pm1 id ofs = Some fl) ∨
               (∃ b ofs', In (id, b, ofs') flat_ids /\ Integers.Ptrofs.intval ofs' = ofs).
Proof.
  induction 1.
  - intuition.
  - intros id' ofs' fl' Hget.
    edestruct IHassign_global_params as [Hleft|Hright]; eauto.
    { subst.
      destruct (Pos.eq_dec id id'); subst.
      { destruct (Z.eq_dec (Integers.Ptrofs.intval ofs) ofs'); subst.
        { right. do 2 eexists; split; eauto.
          left; eauto. }
        { rewrite ParamMap.gso in Hleft; last by (right; congruence).
          eauto. }
      }
      rewrite ParamMap.gso in Hleft; auto.
    }
    right. clear -Hright. destruct Hright as (?&?&?&?).
    do 2 eexists; split; eauto. right. eauto.
Qed.

Lemma assign_global_params_some_in_combine flat_ids pm1 vs pm2 :
  assign_global_params flat_ids pm1 vs pm2 ->
  ∀ id ofs fl, ParamMap.get pm2 id ofs = Some fl ->
               (ParamMap.get pm1 id ofs = Some fl) ∨
                 (∃ b ofs', In ((id, b, ofs'), (Values.Vfloat fl)) (List.combine flat_ids vs) /\
                              Integers.Ptrofs.intval ofs' = ofs).
Proof.
  induction 1.
  - intuition.
  - intros id' ofs' fl' Hget.
    edestruct IHassign_global_params as [Hleft|Hright]; eauto.
    { subst.
      destruct (Pos.eq_dec id id'); subst.
      { destruct (Z.eq_dec (Integers.Ptrofs.intval ofs) ofs'); subst.
        { right. do 2 eexists; split; eauto.
          rewrite ParamMap.gss in Hleft. inv Hleft. left; eauto. }
        { rewrite ParamMap.gso in Hleft; last by (right; congruence).
          eauto. }
      }
      rewrite ParamMap.gso in Hleft; auto.
    }
    right. clear -Hright. destruct Hright as (?&?&?&?).
    do 2 eexists; split; eauto. right. eauto.
Qed.

Lemma assign_global_params2_is_id_alloc flat_ids vs1 vs2 pm1 pm1' pm2 pm2' :
  assign_global_params flat_ids pm1 vs1 pm1' ->
  assign_global_params flat_ids pm2 vs2 pm2' ->
  (∀ id, ParamMap.is_id_alloc pm1 id = ParamMap.is_id_alloc pm2 id) ->
  ∀ id, ParamMap.is_id_alloc pm1' id = ParamMap.is_id_alloc pm2' id.
Proof.
  intros Hassign.
  revert vs2 pm2 pm2'.
  induction Hassign => vs2 pm2 pm2'.
  { intros Hassign2. inv Hassign2. eauto. }
  { intros Hassign2 Hmatch.
    inv Hassign2.
    eapply IHHassign.
    { eauto. }
    intros id'.
    destruct (Pos.eq_dec id id'); subst.
    { rewrite !is_id_set_same //. }
    { rewrite !is_id_set_other //; try congruence. }
  }
Qed.


Lemma assign_global_params2_some_in_combine flat_ids vs1 vs2 pm1 pm1' pm2 pm2' :
  assign_global_params flat_ids pm1 vs1 pm1' ->
  assign_global_params flat_ids pm2 vs2 pm2' ->
  ∀ id ofs fl1, ParamMap.get pm1' id ofs = Some fl1 ->
                (ParamMap.get pm1 id ofs = Some fl1 /\
                 ParamMap.get pm2' id ofs = ParamMap.get pm2 id ofs
                ) ∨
                 (∃ fl2 b ofs', In (((id, b, ofs'), (Values.Vfloat fl1)), (Values.Vfloat fl2))
                                  (List.combine (List.combine flat_ids vs1) vs2) /\
                              ParamMap.get pm2' id ofs = Some fl2 /\
                              Integers.Ptrofs.intval ofs' = ofs).
Proof.
  intros Hassign.
  revert vs2 pm2 pm2'.
  induction Hassign => vs2 pm2 pm2'.
  - intros Hassign2. inv Hassign2. intros.
    left. eauto.
  - intros Hassign2 id' ofs' fl' Hget.
    inv Hassign2.
    edestruct IHHassign as [(Hget1&Hget2)|Hright].
    { eapply H8. }
    { eauto. }
    { destruct (Pos.eq_dec id id'); subst.
      { destruct (Z.eq_dec (Integers.Ptrofs.intval ofs) ofs'); subst.
        { right.
          rewrite ParamMap.gss in Hget1. inv Hget1.
          simpl.
          do 3 eexists; split; eauto; split; auto.
          rewrite Hget2. rewrite gss //.
        }
        { rewrite ParamMap.gso in Hget1; last by (right; congruence).
          rewrite ParamMap.gso in Hget2; last by (right; congruence).
          eauto. }
      }
      left.
      rewrite ParamMap.gso in Hget1; auto.
      rewrite ParamMap.gso in Hget2; auto.
    }
    right. clear -Hright. destruct Hright as (?&?&?&?&?&?).
    do 3 eexists; split; simpl; eauto.
Qed.

Lemma reserve_global_param_get ids pm1 pm2 :
  reserve_global_params ids pm1 pm2 ->
  ∀ id ofs, ParamMap.get pm2 id ofs = ParamMap.get pm1 id ofs.
Proof.
  induction 1; auto.
  subst. intros. rewrite IHreserve_global_params gr //.
Qed.

Lemma reserve_global_params_same pmstart pm1 pm2 :
  reserve_global_params (pr_parameters_ids prog) pmstart pm1 ->
  reserve_global_params (pr_parameters_ids tprog) pmstart pm2 ->
  pm1 = pm2.
Proof.
  rewrite parameters_ids_preserved.
  intros. eapply reserve_global_params_determ; eauto.
Qed.

Lemma reserve_global_params_is_id_alloc_true ids pm1 pm2 id :
  reserve_global_params ids pm1 pm2 ->
  is_id_alloc pm2 id = true ->
  (is_id_alloc pm1 id = true \/ In id ids).
Proof.
  induction 1.
  - auto.
  - intros His. subst. destruct IHreserve_global_params.
    { eauto. }
    { destruct (Pos.eq_dec id id0).
      { subst. right. by left. }
      { rewrite ParamMap.is_id_reserve_other in H; auto. }
    }
    right. by right.
Qed.

Lemma math_idents_not_in_parameters id :
  In id math_idents -> ¬ In id (pr_parameters_ids prog).
Proof.
  destruct TRANSL as (?&?&?&?&?&Hcheck).
  clear -Hcheck.
  intros Hin1 Hin2.
  rewrite /pr_parameters_ids in Hin2.
  apply in_map_iff in Hin2 as (((?&?)&?)&Heq&Hin).
  subst. revert Hcheck.
  rewrite Forall_forall => Hcheck. eapply Hcheck in Hin.
  auto.
Qed.

Lemma In_flatten_parameter_list_id id b ofs :
  In (id, b, ofs) (flatten_parameter_list (pr_parameters_vars tprog)) ->
  In id (pr_parameters_ids tprog).
Proof.
  rewrite /pr_parameters_ids.
  induction (pr_parameters_vars _).
  - inversion 1.
  - destruct a as ((?&[])&?) => //=;
    try (destruct 1 as [Hleft|Hright]; [ left; congruence | right; eauto ]).
    rewrite /flatten_parameter_list/=.
    intros [Hleft|Hright]%in_app_or.
    { rewrite /parameter_basic_to_list/data_basic_to_list/= in Hleft.
      apply in_combine_l in Hleft. apply repeat_spec in Hleft. left; congruence. }
    { right. eauto. }
Qed.

Lemma set_global_params_no_shadow vs pm :
  set_global_params (pr_parameters_ids tprog) (flatten_parameter_list (pr_parameters_vars tprog)) vs empty pm ->
  param_mem_no_shadow_mathlib pm.
Proof.
  destruct 1 as (pm'&Hres&Hassign).
  rewrite /param_mem_no_shadow_mathlib.
  apply Forall_forall. intros x Hin.
  destruct (is_id_alloc _ _) eqn:His; auto.
  exploit assign_global_params_is_id_alloc_in_flat1; eauto.
  intros Hcases.
  assert (In x (pr_parameters_ids prog)).
  {
    destruct Hcases as [Hpm'|Hin'].
    {
      exploit reserve_global_params_is_id_alloc_true; eauto.
      rewrite is_id_empty.
      intros [Hemp|Hshadow]; first congruence.
      rewrite parameters_ids_preserved in Hshadow.
      auto.
    }
    {
      destruct Hin' as (b&ofs'&Hin').
      apply In_flatten_parameter_list_id in Hin'.
      rewrite parameters_ids_preserved in Hin'. auto.
    }
  }
  exploit (math_idents_not_in_parameters); try eassumption.
  intuition.
Qed.

Lemma set_global_params_match_param_mem_none vs1 pm1 vs2 pm2:
  set_global_params (pr_parameters_ids prog) (flatten_parameter_list (pr_parameters_vars prog)) vs1 empty pm1 ->
  set_global_params (pr_parameters_ids tprog) (flatten_parameter_list (pr_parameters_vars tprog)) vs2 empty pm2 ->
  match_param_mem_none pm1 pm2.
Proof.
  intros (pm1'&Hreserve1&Hassign1).
  intros (pm2'&Hreserve2&Hassign2).
  intros id Halloc_false.
  rewrite -Halloc_false.
  eapply assign_global_params2_is_id_alloc.
  { eauto. }
  { rewrite flatten_parameter_list_tprog. eauto. }
  intros. cut (pm1' = pm2'); first by congruence.
  eapply reserve_global_params_same; eauto.
Qed.

Lemma initial_states_match_param_none  d1 d2 p1 p2 f1 f2 fn1 fn2 t1 t2 K1 K2 e1 e2 m1 m2 pm1 pm2:
  initial_state prog d1 p1 (Start f1 fn1 t1 K1 e1 m1 pm1) ->
  initial_state tprog d2 p2 (Start f2 fn2 t2 K2 e2 m2 pm2) ->
  match_param_mem_none pm1 pm2.
Proof.
  intros Hinit1 Hinit2.
  inv Hinit1; inv Hinit2.
  eapply set_global_params_match_param_mem_none; eauto.
Qed.


Lemma In_parameter_basic_to_list_inv id b ofs i b' oe :
  In (id, b, ofs) (parameter_basic_to_list (i, b', oe)) ->
  id = i /\ match b' with
            | Barray bu _ => b = bu
            | _ => b = b'
            end.
Proof.
  rewrite /parameter_basic_to_list/data_basic_to_list/=.
  destruct b'; try (inversion 1; subst; intuition; eauto; congruence).
  intros Hin. apply in_combine_l in Hin. apply repeat_spec in Hin. inv Hin; eauto.
Qed.

Lemma flatten_parameter_constraints_found_parameters :
  flatten_parameter_constraints prog =
    (map (λ '(_, v, _), vd_constraint v) (flatten_ident_variable_list found_parameters)).
Proof.
  clear.
  rewrite /flatten_parameter_constraints.
  rewrite /flatten_parameter_variables.
  rewrite pr_parameters_vars_found_parameters /=.
  specialize (found_parameters_spec) => Hmmap.
  apply mmap_inversion in Hmmap.
  revert Hmmap. generalize (pr_parameters_vars prog).
  induction found_parameters.
  - rewrite //=.
  - intros l' Hforall2. inv Hforall2.
    rewrite /=.
    destruct a as ((?&?)&?).
    exploit find_parameter_lookup_def_ident_prog; eauto. intros ->.
    rewrite /flatten_ident_variable_list/=.
    rewrite ?map_app; f_equal.
    eapply IHl; eauto.
Qed.

Lemma count_down_ofs_len n : length (count_down_ofs n) = n.
Proof.
  induction n => //=.
  rewrite IHn //.
Qed.

Lemma count_up_ofs_len n : length (count_up_ofs n) = n.
Proof.
  rewrite /count_up_ofs rev_length count_down_ofs_len //.
Qed.

Variable params_in_rect: in_list_rectangle params (parameter_list_rect prog).

Lemma in_flatten_5tuple id b ofs fl1 fl2 :
  (In (id, b, ofs, Values.Vfloat fl1, Values.Vfloat fl2)
      (combine (combine (flatten_parameter_list (pr_parameters_vars prog)) (map R2val params))
         (map R2val (param_unmap params)))) ->
  (∃ r v oe, In (id, v, oe) found_parameters /\
               in_interval r (constraint_to_interval (vd_constraint v)) /\
               fl1 = IRF r /\
               fl2 = IRF (unconstrain_fn (vd_constraint v) r)).
Proof.
  intros Hin.
  move: params_in_rect.
  rewrite /parameter_list_rect.
  rewrite pr_parameters_vars_found_parameters in Hin.
  rewrite /param_unmap in Hin.
  rewrite flatten_parameter_constraints_found_parameters in Hin.
  rewrite flatten_parameter_constraints_found_parameters.
  revert Hin.
  clear params_in_rect.
  generalize params. clear params.
  induction (found_parameters) => params Hin Hin_rect.
  { simpl in Hin. inversion Hin. }
  { destruct a as ((?&?)&?).
    simpl in Hin.
    rewrite /flatten_ident_variable_list in Hin Hin_rect.
    rewrite /flatten_parameter_list in Hin Hin_rect.
    rewrite ?map_cons in Hin.
    rewrite concat_map in Hin.
    rewrite /= in Hin.
    rewrite {1}/parameter_basic_to_list/data_basic_to_list/= in Hin Hin_rect.
    destruct (vd_type v).
    { rewrite /= in Hin.
      destruct params as [| ? params']; first by rewrite //=.
      simpl in Hin. destruct Hin as [Hleft|Hrec].
      { inv Hleft. do 3 eexists. split; first by left. simpl in Hin_rect. inv Hin_rect; eauto. }
      edestruct (IHl params') as (?&?&?&Hin).
      {
        rewrite /flatten_ident_variable_list.
        rewrite /flatten_parameter_list.
        rewrite ?map_cons.
        rewrite concat_map.
        eapply Hrec.
      }
      { inv Hin_rect. eauto. }
      do 3 eexists. intuition eauto. right; eauto.
    }
    { rewrite /= in Hin.
      destruct params as [| ? params']; first by rewrite //=.
      simpl in Hin. destruct Hin as [Hleft|Hrec].
      { inv Hleft. do 3 eexists. split; first by left. simpl in Hin_rect. inv Hin_rect; eauto. }
      edestruct (IHl params') as (?&?&?&Hin).
      {
        rewrite /flatten_ident_variable_list.
        rewrite /flatten_parameter_list.
        rewrite ?map_cons.
        rewrite concat_map.
        eapply Hrec.
      }
      { inv Hin_rect. eauto. }
      do 3 eexists. intuition eauto. right; eauto.
    }
    2: { rewrite /= in Hin.
      destruct params as [| ? params']; first by rewrite //=.
      simpl in Hin. destruct Hin as [Hleft|Hrec].
      { inv Hleft. do 3 eexists. split; first by left. simpl in Hin_rect. inv Hin_rect; eauto. }
      edestruct (IHl params') as (?&?&?&Hin).
      {
        rewrite /flatten_ident_variable_list.
        rewrite /flatten_parameter_list.
        rewrite ?map_cons.
        rewrite concat_map.
        eapply Hrec.
      }
      { inv Hin_rect. eauto. }
      do 3 eexists. intuition eauto. right; eauto.
    }
    {
      move: Hin Hin_rect.
      generalize params.
      specialize (count_up_ofs_len (Z.to_nat z)).
      generalize (count_up_ofs (Z.to_nat z)).
      induction (Z.to_nat z) => lofs Hlen params' Hin Hin_rect.
      { simpl in Hin.
        edestruct (IHl params') as (?&?&?&Hin').
        { rewrite /flatten_ident_variable_list.
          rewrite /flatten_parameter_list.
          rewrite ?map_cons.
          rewrite concat_map.
          eapply Hin. }
        { rewrite /= in Hin_rect. eauto. }
        do 3 eexists; intuition eauto. right; eauto.
      }
      destruct params' as [| ? params'].
      { rewrite //= in Hin Hin_rect.
        rewrite combine_nil in Hin Hin_rect.
        inv Hin.
      }
      simpl in Hin.
      destruct lofs.
      { inversion Hlen. }
      simpl in Hin. destruct Hin as [Hleft|Hrec].
      { inv Hleft. do 3 eexists. split; first by left. inv Hin_rect. eauto. }
      inv Hin_rect.
      eapply IHn; eauto.
    }
  }
Qed.

Lemma set_global_params_match_param_mem_some pm1 pm2:
  set_global_params (pr_parameters_ids prog)
    (flatten_parameter_list (pr_parameters_vars prog)) (map R2val params) empty pm1 ->
  set_global_params (pr_parameters_ids tprog)
    (flatten_parameter_list (pr_parameters_vars tprog)) (map R2val (param_unmap params)) empty pm2 ->
  match_param_mem_some pm1 pm2.
Proof.
  intros Hset1 Hset2.
  destruct Hset1 as (pm1'&Hres1&Hassign1).
  destruct Hset2 as (pm2'&Hres2&Hassign2).
  intros id ofs fl1 Hget.
  exploit assign_global_params2_some_in_combine.
  { eapply Hassign1. }
  { rewrite -flatten_parameter_list_tprog. eapply Hassign2. }
  { eauto. }
  intros [Hget_pm1'| Hright].
  { exfalso.
    erewrite reserve_global_param_get in Hget_pm1'; eauto.
    rewrite gempty in Hget_pm1'. intuition congruence. }
  {
    destruct Hright as (fl2&b&ofs'&Hin&Hget2&Hofs).
    edestruct (in_flatten_5tuple) as (r&v&oe&Hin1&Hinterval&Hfl1&Hfl2); eauto.
    exploit (fpmap_spec); eauto. intros Hfpmap.
    do 2 eexists; split; [| split]; eauto.

    subst.
    intros.
    eapply eval_constrained_fun'; eauto.
    eapply set_global_params_no_shadow; eexists; eauto.
  }
Qed.

Lemma initial_states_match_param_some f1 f2 fn1 fn2 t1 t2 K1 K2 e1 e2 m1 m2 pm1 pm2:
  initial_state prog data (map R2val params) (Start f1 fn1 t1 K1 e1 m1 pm1) ->
  initial_state tprog data (map R2val (param_unmap params)) (Start f2 fn2 t2 K2 e2 m2 pm2) ->
  match_param_mem_some pm1 pm2.
Proof.
  intros Hinit1 Hinit2.
  inv Hinit1; inv Hinit2.
  eapply set_global_params_match_param_mem_some; eauto.
Qed.

Lemma fpmap_cases id fe:
  fpmap id = Some fe ->
  (∃ c, fe = (unconstrained_to_constrained_fun c)).
Proof.
  rewrite /fpmap. induction found_parameters as [| ((?&?)&?)].
  - rewrite //=.
  - simpl. destruct (Pos.eq_dec _ _).
    * rewrite /unconstrained_to_constrained. inversion 1; subst. eexists; eauto.
    * eauto.
Qed.

Lemma eval_const_float en m pm t v v0 :
  eval_expr tge en m pm t (Econst_float v Breal) v0 ->
  v0 = Values.Vfloat v.
Proof.
  { intros Heval. inv Heval; try (inv H; done); eauto. }
Qed.


Lemma eval_expr_fpmap_ctxt id en m pm t fe e v vres :
  fpmap id = Some fe ->
  typeof e = Breal ->
  eval_expr tge en m pm t e (Values.Vfloat v) ->
  eval_expr tge en m pm t (fe (Econst_float v Breal)) vres ->
  eval_expr tge en m pm t (fe e) vres.
Proof.
  intros (c&->)%fpmap_cases Hreal.
  destruct c => //=.
  { intros. exploit eval_const_float; eauto. intros; subst; intuition. }
  { intros Heval1 Heval2.
    inv Heval2.
    {  econstructor; eauto.
       inv H4; try (inv H; done). econstructor; eauto.
      inv H3. subst. econstructor; auto.
      exploit eval_const_float; eauto; intros; subst; eauto. }
    inv H.
    inv H.
  }
  { intros Heval1 Heval2.
    inv Heval2; try (inv H; done).
    { econstructor; eauto.
      exploit eval_const_float; eauto; intros; subst; eauto.
      inv H5; try (inv H; done). econstructor; eauto.
      inv H3. subst. econstructor; auto.
      econstructor; eauto.
      { econstructor. }
      subst.
      rewrite Hreal /=.
      inv H1. simpl in H13.
      exploit eval_const_float; eauto; intros; subst; eauto.
      clear H12.
      exploit eval_const_float; eauto; intros; subst; eauto.
      inv H.
      inv H.
    }
  }
  { intros Heval1 Heval2.
    inv Heval2; try (inv H; done).
    { econstructor; eauto.
      exploit eval_const_float; eauto; intros; subst; eauto.
      inv H5; try (inv H; done). econstructor; eauto.
      inv H8. inv H3. subst. econstructor; eauto.
      econstructor; eauto.
      exploit eval_const_float; eauto; intros; subst; eauto.
      inv H.
      inv H.
    }
  }
Qed.

Lemma reserve_global_params_wf pm:
  reserve_global_params (pr_parameters_ids prog) ParamMap.empty pm ->
  wf_param_mem pm.
Proof.
  rewrite /wf_param_mem/fpmap/pr_parameters_ids.
  specialize (found_parameters_spec) as Heqn.
  remember (pr_parameters_vars prog) as pvars eqn:Heqvars. clear Heqvars.
  remember (map (λ '(id, _, _), id) pvars) as pids eqn:Heqpids.
  intros Hassign. revert Heqpids Heqn.
  generalize (found_parameters).
  generalize pvars. clear pvars.
  induction Hassign.
  - intros pvars found Heqmap Heqfound id.
    { destruct pvars; last by (simpl in Heqmap; inv Heqmap).
      inversion Heqfound; subst. rewrite //=. }
  - intros pvars found Heqmap Heqfound id' His.
    destruct pvars as [|].
    { simpl in Heqmap. inv Heqmap. }
    simpl in Heqmap. inv Heqmap.
    simpl in Heqfound.
    monadInv Heqfound.
    simpl. destruct x as ((?&?)&?).
    destruct p as ((?&?)&?).
    eapply find_parameter_ident_match in EQ as (<-&<-&?).
    destruct (Pos.eq_dec i0 id').
    { subst. intros. exfalso.
      exploit reserve_global_preserves_alloc; eauto.
      erewrite reserve_is_alloc; eauto.
    }
    intros. eapply IHHassign; eauto.
Qed.

Lemma assign_global_params_wf pm bs vs pm':
  wf_param_mem pm ->
  assign_global_params bs pm vs pm' ->
  wf_param_mem pm'.
Proof.
  intros Hwf Hassign.
  rewrite /wf_param_mem.
  intros id Hid.
  eapply Hwf. eapply assign_global_params_preserves_alloc; eauto.
Qed.

Lemma set_global_params_wf pm flat vs :
  set_global_params (pr_parameters_ids prog) flat vs ParamMap.empty pm ->
  wf_param_mem pm.
Proof.
  intros (?&Hres&Hassign).
  eapply assign_global_params_wf; eauto.
  eapply reserve_global_params_wf; eauto.
Qed.

Lemma wf_param_mem_init d f fn t K e m pm:
  initial_state prog d (map R2val params) (Start f fn t K e m pm) ->
  wf_param_mem pm.
Proof.
  intros Hinit. inv Hinit.
  eapply set_global_params_wf; eauto.
Qed.

Lemma evaluation_preserved:
  forall en m pm0 pm1 t,
    valid_env en ->
    match_param_mem pm0 pm1 ->
    wf_param_mem pm0 ->
    env_no_shadow_mathlib en ->
      (forall e v, eval_expr ge en m pm0 t e v ->
                   forall e', transf_expr fpmap e = OK e' ->
                              eval_expr tge en m pm1 t e' v)
  /\  (forall el vl, eval_exprlist ge en m pm0 t el vl ->
                     forall el', transf_exprlist fpmap el = OK el' ->
                                 eval_exprlist tge en m pm1 t el' vl)
  /\  (forall e loc ofs, eval_plvalue ge en m pm0 t e loc ofs ->
                           match e with
                           | Eindexed e el ty =>
                               forall el', transf_exprlist fpmap el = OK el' ->
                                           eval_plvalue tge en m pm1 t (Eindexed e el' ty)
                                             loc ofs
                           | _ => eval_plvalue tge en m pm1 t e loc ofs
                           end)
  /\  (forall e loc ofs s, eval_lvalue ge en m pm0 t e loc ofs s ->
                           match e with
                           | Eindexed e el ty =>
                               forall el', transf_exprlist fpmap el = OK el' ->
                                           eval_lvalue tge en m pm1 t (Eindexed e el' ty)
                                             loc ofs s
                           | _ => eval_lvalue tge en m pm1 t e loc ofs s
                           end).
Proof.
  intros en m pm0 pm1 t Hval Hmatch Hwf Hnoshadow.
  apply (eval_exprs_ind ge en m pm0 t); intros.
  { simpl in H; inversion H; econstructor; eauto. }
  { simpl in H; inversion H; econstructor; eauto. }
  { monadInv H2. econstructor; eauto.
    erewrite typeof_transf_expr; eauto. }
  { monadInv H4. econstructor; eauto.
    erewrite typeof_transf_expr; eauto.
    erewrite (typeof_transf_expr _ x0); eauto.
  }
  { subst.
    edestruct (functions_translated) as (ef'&?&Htransf'); eauto.
    monadInv Htransf'.
    monadInv H7.
    econstructor; eauto.
    eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
  }
  { monadInv H. econstructor. }
  { monadInv H2. econstructor; eauto. erewrite typeof_transf_expr; eauto. }
  {
    inversion H; subst.
    { simpl in H2.
      destruct Hmatch as (Hmatch&_).
      exploit Hmatch; eauto. intros (fe&fl'&Hget'&Hfpmap&Heval).
      rewrite Hfpmap in H2. destruct ty; inversion H2; subst.
      eapply eval_expr_fpmap_ctxt; eauto.
      econstructor; eauto.
    }
    { simpl in H2.
      destruct Hmatch as (Hmatch&_).
      apply bind_inversion in H2 as (al'&Htransf'&Hret).
      exploit Hmatch; eauto. intros (fe&fl'&Hget'&Hfpmap&Heval).
      rewrite Hfpmap in Hret. destruct ty; inversion Hret; subst.
      eapply eval_expr_fpmap_ctxt; eauto.
      econstructor; eauto.
    }
  }
  {
    inversion H; subst.
    { simpl in H2.
      rewrite Hval in H2; last by congruence.
      { inversion H2; subst. econstructor; eauto. }
    }
    { simpl in H2.
      rewrite Hwf in H2; auto.
      { inversion H2; subst. econstructor; eauto. }
    }
    { simpl in H2.
      rewrite Hwf in H2; auto.
      { apply bind_inversion in H2 as (al'&Htransf'&Hret).
        inv Hret.
        econstructor; eauto.
      }
    }
  }

  (* list *)
  { monadInv H. simpl. econstructor; eauto. }
  { monadInv H3. simpl. econstructor; eauto. }

  (* lvalue *)
  { simpl. econstructor; eauto. }
  { simpl. econstructor; eauto. }

  { simpl. econstructor; eauto. }
  { simpl. econstructor; eauto.
    { destruct Hmatch as (_&Hmatch). eapply Hmatch; auto. }
    { rewrite symbols_preserved; auto. }
  }

  { simpl. try econstructor; eauto.
    destruct Hmatch as (_&Hmatch). eapply Hmatch; auto. }
Qed.

Definition valid_env_full en := valid_env en /\ env_no_shadow_mathlib en.
Definition match_param_mem_full pm0 pm1 :=
  match_param_mem pm0 pm1 /\
  wf_param_mem pm0.

Lemma eval_expr_preserved:
  forall en m pm0 pm1 t e e' v,
  valid_env_full en ->
  match_param_mem_full pm0 pm1 ->
  transf_expr fpmap e = OK e' ->
  eval_expr ge en m pm0 t e v ->
  eval_expr tge en m pm1 t e' v.
Proof.
  rewrite /valid_env_full/match_param_mem_full.
  intros.
  eapply evaluation_preserved; intuition eauto.
Qed.

Lemma eval_lvalue_preserved:
  forall en m pm0 pm1 t e loc ofs s,
  valid_env_full en ->
  match_param_mem_full pm0 pm1 ->
  eval_lvalue ge en m pm0 t e loc ofs s ->
  match e with
  | Eindexed e el ty =>
      forall el', transf_exprlist fpmap el = OK el' ->
                  eval_lvalue tge en m pm1 t (Eindexed e el' ty)
                  loc ofs s
  | _ => eval_lvalue tge en m pm1 t e loc ofs s
  end.
Proof.
  rewrite /valid_env_full/match_param_mem_full.
  intros.
  eapply evaluation_preserved; intuition eauto.
Qed.

Lemma eval_plvalue_preserved:
  forall en m pm0 pm1 t e loc ofs,
  valid_env_full en ->
  match_param_mem_full pm0 pm1 ->
  eval_plvalue ge en m pm0 t e loc ofs ->
  match e with
  | Eindexed e el ty =>
      forall el', transf_exprlist fpmap el = OK el' ->
                  eval_plvalue tge en m pm1 t (Eindexed e el' ty)
                  loc ofs
  | _ => eval_plvalue tge en m pm1 t e loc ofs
  end.
Proof.
  rewrite /valid_env_full/match_param_mem_full.
  intros.
  eapply evaluation_preserved; intuition eauto.
Qed.

Lemma eval_exprlist_preserved:
  forall en m pm0 pm1 t el el' v,
  valid_env_full en ->
  match_param_mem_full pm0 pm1 ->
  transf_exprlist fpmap el = OK el' ->
  eval_exprlist ge en m pm0 t el v ->
  eval_exprlist tge en m pm1 t el' v.
Proof.
  rewrite /valid_env_full/match_param_mem_full.
  intros.
  eapply evaluation_preserved; intuition eauto.
Qed.

Inductive match_cont: cont -> cont -> Prop :=
  | match_Kseq: forall s s' k k'
      (TRS: transf_statement fpmap s = OK s')
      (MCONT: match_cont k k'),
      match_cont (Kseq s k) (Kseq s' k')
  | match_Kstop:
      match_cont Kstop (Kseq (Starget fcorrection) Kstop).

Inductive match_states: state -> state -> Prop :=
  | match_start_states: forall f f' s s' t e m pm pm'
      (TRF: transf_function fpmap fcorrection f = OK f')
      (TRS: transf_statement fpmap s = OK s')
      (VE: valid_env_full e)
      (MPM: match_param_mem_full pm pm'),
      match_states (Start f s t Kstop e m pm)
                   (Start f' (Ssequence s' (Starget fcorrection)) t Kstop e m pm')
  | match_regular_states: forall f f' s s' t k k' e m pm pm'
      (TRF: transf_function fpmap fcorrection f = OK f')
      (TRS: transf_statement fpmap s = OK s')
      (MCONT: match_cont k k')
      (VE: valid_env_full e)
      (MPM: match_param_mem_full pm pm'),
      match_states (State f s t k e m pm)
                   (State f' s' t k' e m pm')
  | match_return_states: forall f f' t e m pm pm'
      (TRF: transf_function fpmap fcorrection f = OK f')
      (VE: valid_env_full e)
      (MPM: match_param_mem_full pm pm'),
      match_states (Return f (IRF t) e m pm)
                   (Return f' (IRF (target_map data (map R2val (param_unmap params)) t)) e m pm').

Axiom IRF_0 : IRF 0 = Floats.Float.zero.

Lemma assign_global_params_app_inv ids1 ids2 vs pm0 pm :
  assign_global_params (ids1 ++ ids2) pm0 vs pm ->
  ∃ pm' vs1 vs2,
    vs = List.app vs1 vs2 /\
    length vs1 = length ids1 /\
    assign_global_params ids1 pm0 vs1 pm' /\
    assign_global_params ids2 pm' vs2 pm.
Proof.
  revert vs pm0 pm.
  induction ids1.
  { intros vs pm0 pm. simpl. exists pm0, nil, vs. rewrite //=; intuition eauto.
    econstructor. }
  { intros vs pm0 pm Hassign.
    inversion Hassign. subst. exploit IHids1; eauto. intros (pm'&vs1'&vs2'&Heq1&Hlen1&Hassign1&Hassign2).
    eexists pm', (_ :: vs1'), vs2'.
    split; eauto.
    { simpl. rewrite Heq1 //=. }
    split; simpl; auto.
    split; eauto.
    { econstructor; eauto. }
  }
Qed.

Lemma list_apply_app {A B: Type} (fs1 fs2: list (A -> B)) (xs1 xs2: list A) :
  length fs1 = length xs1 ->
  list_apply (fs1 ++ fs2) (xs1 ++ xs2) =
  (list_apply fs1 xs1 ++ list_apply fs2 xs2)%list.
Proof.
  revert xs1. induction fs1 => xs1.
  { rewrite //=. destruct xs1; by inversion 1.  }
  { rewrite //=. destruct xs1; first by inversion 1.
    simpl. inversion 1. rewrite /list_apply/=. f_equal. eauto.
  }
Qed.

Lemma list_plus_app (xs1 xs2: list R) :
  list_plus (xs1 ++ xs2) = list_plus xs1 + list_plus xs2.
Proof.
  induction xs1 => //=; try nra.
Qed.

Lemma length_array_basic_to_list1 i b z o :
  length (parameter_basic_to_list (i, Barray b z, o)) = Z.to_nat z.
Proof.
  rewrite /parameter_basic_to_list/data_basic_to_list/=.
  rewrite combine_length.
  rewrite repeat_length.
  rewrite count_up_ofs_len.
  rewrite Nat.min_id //.
Qed.

Lemma assign_global_params_not_in_nochange i ofs bs pm0 vs pm :
  assign_global_params bs pm0 vs pm ->
  (∀ b ofs', In (i, b, ofs') bs -> Integers.Ptrofs.intval ofs <> Integers.Ptrofs.intval ofs') ->
  get pm i (Integers.Ptrofs.intval ofs) = get pm0 i (Integers.Ptrofs.intval ofs).
Proof.
  intros Hassign.
  induction Hassign => Hnin; auto.
  rewrite IHHassign; last first.
  { intros ?? Hin'. eapply Hnin. right; eauto. }
  subst. rewrite gso //.
  destruct (Pos.eq_dec i id); last by auto.
  subst.
  destruct (Z.eq_dec (Integers.Ptrofs.intval ofs) (Integers.Ptrofs.intval ofs0)); last by auto.
  exfalso.
  eapply Hnin; first by left. eauto.
Qed.
  
Lemma assign_global_params_tail_not_in i b ofs bs pm0 v vs pm :
  assign_global_params ((i, b, ofs) :: bs) pm0 (Values.Vfloat v :: vs) pm ->
  (∀ b ofs', In (i, b, ofs') bs -> Integers.Ptrofs.intval ofs <> Integers.Ptrofs.intval ofs') ->
  get pm i (Integers.Ptrofs.intval ofs) = Some v.
Proof.
  intros Hassign Hnin.
  inv Hassign.
  exploit assign_global_params_not_in_nochange; eauto => ->.
  rewrite gss //.
Qed.

Inductive flat_nodups {A: Type} : list (AST.ident * A * Integers.Ptrofs.int) -> Prop :=
  | flat_nodups_nil :
    flat_nodups nil
  | flat_nodups_cons bs id a ofs :
     (∀ b ofs', In (id, b, ofs') bs -> Integers.Ptrofs.intval ofs <> Integers.Ptrofs.intval ofs') ->
     flat_nodups bs ->
     flat_nodups ((id, a, ofs) :: bs).

Lemma flatten_parameter_list_cons hd tl :
  (flatten_parameter_list (hd :: tl) = parameter_basic_to_list hd ++ flatten_parameter_list tl)%list.
Proof.
  rewrite /flatten_parameter_list//=.
Qed.

Lemma flat_nodups_parameters : flat_nodups (flatten_parameter_list (pr_parameters_vars tprog)).
Proof.
  rewrite flatten_parameter_list_tprog.
  rewrite pr_parameters_vars_found_parameters.
  induction found_parameters.
  { econstructor. }
  { rewrite /=. destruct a as ((id, v), e).
    rewrite flatten_parameter_list_cons.
    rewrite /parameter_basic_to_list/data_basic_to_list/=.
    { destruct (vd_type v) => //=.
      { econstructor; last eauto.
        intros b' ofs' Hin.
Abort.        

Lemma eval_correction e m pm0 pm t
  (ENOSHADOW : env_no_shadow_param e pm)
  (VE : valid_env_full e) :
  assign_global_params (flatten_parameter_list (pr_parameters_vars tprog)) pm0
    (map R2val (param_unmap params)) pm ->
  eval_expr tge e m pm t fcorrection
    (Values.Vfloat (IRF (list_plus (list_apply log_dgs (map val2R (map R2val (param_unmap params))))))).
Proof.
  remember (param_unmap params) as ups.
  rewrite /fcorrection.
  clear Hequps.
  rewrite /log_dgs.
  rewrite flatten_parameter_constraints_found_parameters.
  rewrite flatten_parameter_list_tprog.
  rewrite pr_parameters_vars_found_parameters.
  revert ups pm0.
  rewrite //=.
  rewrite /flatten_parameter_list/=.
  rewrite /flatten_ident_variable_list//=.
  induction (found_parameters).
  { rewrite //=. intros ups pm0.
    inversion 1; subst.
    rewrite IRF_0. econstructor. }
  { intros ups pm0.
    destruct a as ((?&?)&?).
    rewrite /=/change_of_variable_correction/=.
    destruct (vd_constraint v) eqn:Hvd.
    { rewrite /=.
      rewrite map_app.
      destruct (vd_type v).
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=. rewrite Rplus_0_l. destruct ups; inv H6.
        eapply IHl; eauto.
      }
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=. rewrite Rplus_0_l. destruct ups; inv H6.
        eapply IHl; eauto.
      }
      {
        intros Hassign.
        eapply assign_global_params_app_inv in Hassign as (pm'&vs1&vs2&Heq1&Hlen&Hassign1&Hassign2).
        apply map_eq_app in Heq1 as (ups1&ups2&Heq_ups&Hups1&Hups2).
        rewrite Heq_ups. rewrite ?map_app.
        rewrite list_apply_app; last first.
        { rewrite Hups1. rewrite ?map_length.
          rewrite repeat_length.
          rewrite Hlen length_array_basic_to_list1 //.
        }
        rewrite list_plus_app.
        assert ((list_plus
             (list_apply
                (map log_deriv_constrain_fn
                   (map (λ '(_, v0, _), vd_constraint v0)
                      (repeat (i, {| vd_type := b; vd_constraint := Cidentity |}, o) (Z.to_nat z))))
                (map val2R (map R2val ups1)))) = 0) as Heq0.
        { clear. generalize (map val2R (map R2val ups1)). induction (Z.to_nat z) => //=.
          intros l'. destruct l' => //=. rewrite IHn. nra. }
        rewrite Heq0 Rplus_0_l.
        eapply IHl.
        rewrite Hups2. eauto.
      }
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=. rewrite Rplus_0_l. destruct ups; inv H6.
        eapply IHl; eauto.
      }
    }
    { rewrite /=.
      rewrite map_app.
      destruct (vd_type v) eqn:Hvdty.
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=. econstructor. 
        rewrite -H6 in H.
        (*
          inversion 1; subst.
          induction 


        econstructor.
        { econstructor.

        simpl in H.
        inv H. subst.
        eapply IHl; eauto.
      }
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=. rewrite Rplus_0_l. destruct ups; inv H6.
        eapply IHl; eauto.
      }
      {
        intros Hassign.
        eapply assign_global_params_app_inv in Hassign as (pm'&vs1&vs2&Heq1&Hlen&Hassign1&Hassign2).
        apply map_eq_app in Heq1 as (ups1&ups2&Heq_ups&Hups1&Hups2).
        rewrite Heq_ups. rewrite ?map_app.
        rewrite list_apply_app; last first.
        { rewrite Hups1. rewrite ?map_length.
          rewrite repeat_length.
          rewrite Hlen length_array_basic_to_list1 //.
        }
        rewrite list_plus_app.
        assert ((list_plus
             (list_apply
                (map log_deriv_constrain_fn
                   (map (λ '(_, v0, _), vd_constraint v0)
                      (repeat (i, {| vd_type := b; vd_constraint := Cidentity |}, o) (Z.to_nat z))))
                (map val2R (map R2val ups1)))) = 0) as Heq0.
        { clear. generalize (map val2R (map R2val ups1)). induction (Z.to_nat z) => //=.
          intros l'. destruct l' => //=. rewrite IHn. nra. }
        rewrite Heq0 Rplus_0_l.
        eapply IHl.
        rewrite Hups2. eauto.
      }
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=. rewrite Rplus_0_l. destruct ups; inv H6.
        eapply IHl; eauto.
      }
    }
         *)
Abort.

Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', plus Ssemantics.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inversion MS; simpl in *; subst.
  - (* Start *)
    eexists.
    split.
    { eapply plus_two. econstructor; eauto.
      econstructor; eauto. rewrite //=. }
    { econstructor; eauto. econstructor. }
  - (* Return *)
    inv MCONT.
    inv TRS.
    replace t with (IRF (IFR t)); last first.
    { rewrite IRF_IFR_inv //. }

    eexists; split; last first.
    { econstructor; eauto. }

    rewrite /target_map.
    { eapply plus_three.
      { econstructor; eauto. }
      2: { rewrite Rplus_comm. rewrite -float_add_irf. econstructor. }
      { econstructor. admit. }
      rewrite //=.
    }
  - (* Skip *)
    inv TRS. inv MCONT; subst.
    eexists. split.
    eapply plus_one.
    { econstructor. }
    { econstructor; eauto. }
  - (* Sequence *)
    monadInv TRS.
    eexists. split.
    eapply plus_one.
    { econstructor. }
    { econstructor; eauto. econstructor; eauto. }
  - (* Assignment *)
    monadInv TRS.
    exploit (eval_lvalue_preserved); eauto.
    exploit (eval_expr_preserved); eauto.
    intros Hexpr Hlvalue.
    inv H.
    {
      eexists. split.
      eapply plus_one.
      simpl in EQ.
      assert (fpmap id = None) as Hfpmap.
      { apply VE; congruence. }
      rewrite Hfpmap in EQ. inv EQ.
      econstructor; eauto.
      { erewrite typeof_transf_expr; eauto. }
      { eapply assign_loc_preserved; eauto. }
      { econstructor; eauto. }
    }
    {
      monadInv EQ.
      eexists. split.
      eapply plus_one.
      inv H3.
      assert (fpmap id = None) as Hfpmap.
      { apply VE; congruence. }
      rewrite Hfpmap in EQ2. inv EQ2.
      econstructor; eauto.
      { erewrite typeof_transf_expr; eauto. }
      { eapply assign_loc_preserved; eauto. }
      { econstructor; eauto. }
    }
  - (* Conditional statement *)
    monadInv TRS.
    eexists. split.
    {
      eapply plus_one.
      econstructor.
      { eapply eval_expr_preserved; eauto. }
      { erewrite typeof_transf_expr; eauto.  }
    }
    econstructor; eauto. destruct b; eauto.
  - (* Target *)
    monadInv TRS.
    eexists. split.
    {
    eapply plus_one.
    econstructor.
    { eapply eval_expr_preserved; eauto. }
    }
    econstructor; eauto.
  - (* Tilde *)
    monadInv TRS.
Abort.


Theorem transf_program_correct_change t:
    is_safe prog data (map R2val params) ->
    forward_simulation (Ssemantics.semantics prog data (map R2val params) (IRF t))
      (Ssemantics.semantics tprog data (map R2val (param_unmap params))
         (IRF (target_map data (map R2val (param_unmap params)) t))).
Proof.
  intros Hsafe.
Admitted.

(* TODO: Joe: this doesn't make sense, because we ought to be remapping data/params in target *)
Theorem transf_program_correct tval params':
  forward_simulation (Ssemantics.semantics prog data params' tval) (Ssemantics.semantics tprog data params' tval).
Proof.
  clear -TRANSL.
Admitted.

End PRESERVATION.

Global Instance TransfReparameterizationtLink : TransfLink match_prog.
Admitted.
