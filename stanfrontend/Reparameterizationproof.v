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
    - intros. destruct f; inversion H.
      {  apply bind_inversion in H1 as (?&?&Heq''). inversion Heq''; subst; eauto.
         econstructor; eauto. }
      { subst. econstructor. }
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

Axiom IFR_IRF_inv :
  ∀ x, IFR (IRF x) = x.
Axiom IRF_IFR_inv :
  ∀ x, IRF (IFR x) = x.

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

Axiom exp_ext_spec :
  forall a ge m,
  Events.external_call exp_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m Events.E0 (Values.Vfloat (IRF (exp a))) m.

Axiom exp_ext_no_mem_dep :
  forall a ge m,
  no_mem_dep exp_ef_external ge (Values.Vfloat (IRF a) :: nil) m
    (Values.Vfloat (IRF (exp a))).

Definition expit_ef_external :=
  (AST.EF_external "expit" (AST.mksignature (AST.Tfloat :: nil) (AST.Tret AST.Tfloat)
                            (AST.mkcallconv None false false))).

Axiom global_env_expit :
  exists loc,
  Globalenvs.Genv.find_symbol (globalenv tprog) ($"expit") = Some loc /\
  Globalenvs.Genv.find_funct (globalenv tprog) (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            expit_ef_external
            (Ctypes.Tcons tdouble Ctypes.Tnil)
            tdouble
            (AST.mkcallconv None false false)).

Axiom expit_ext_spec :
  forall a ge m,
  Events.external_call expit_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m Events.E0 (Values.Vfloat (IRF (logit_inv a))) m.

Axiom expit_ext_no_mem_dep :
  forall a ge m,
  no_mem_dep expit_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m (Values.Vfloat (IRF (logit_inv a))).

Definition log_ef_external :=
  (AST.EF_external "log" (AST.mksignature (AST.Tfloat :: nil) (AST.Tret AST.Tfloat)
                            (AST.mkcallconv None false false))).

Axiom global_env_log :
  exists loc,
  Globalenvs.Genv.find_symbol (globalenv tprog) ($"log") = Some loc /\
  Globalenvs.Genv.find_funct (globalenv tprog) (Values.Vptr loc Integers.Ptrofs.zero) =
    Some (Ctypes.External
            log_ef_external
            (Ctypes.Tcons tdouble Ctypes.Tnil)
            tdouble
            (AST.mkcallconv None false false)).

Axiom log_ext_spec :
  forall a ge m,
  Events.external_call log_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m Events.E0 (Values.Vfloat (IRF (ln a))) m.

Axiom log_ext_no_mem_dep :
  forall a ge m,
  no_mem_dep log_ef_external ge
    (Values.Vfloat (IRF a) :: nil) m (Values.Vfloat (IRF (ln a))).

Axiom float_add_irf: forall a b,
  (Floats.Float.add (IRF a) (IRF b)) = IRF (a + b).
Axiom float_sub_irf: forall a b,
  (Floats.Float.sub (IRF a) (IRF b)) = IRF (a - b).
Axiom float_mul_irf: forall a b,
  (Floats.Float.mul (IRF a) (IRF b)) = IRF (a * b).
Axiom IFR_zero :
  IFR (Floats.Float.zero) = 0.

Lemma float_add_irf': forall a b,
  (Floats.Float.add a b) = IRF (IFR a + IFR b).
Proof. intros a b. rewrite -float_add_irf ?IRF_IFR_inv //. Qed.

Lemma float_sub_irf': forall a b,
  (Floats.Float.sub a b) = IRF (IFR a - IFR b).
Proof. intros a b. rewrite -float_sub_irf ?IRF_IFR_inv //. Qed.

Lemma float_mul_irf': forall a b,
  (Floats.Float.mul a b) = IRF (IFR a * IFR b).
Proof. intros a b. rewrite -float_mul_irf ?IRF_IFR_inv //. Qed.

Set Nested Proofs Allowed.
Lemma eval_expr_fun_const pr v :
  eval_expr_fun pr (Econst_float v Breal) = (Values.Vfloat v).
Proof.
  apply eval_expr_fun_spec. econstructor.
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

    destruct (vd_constraint _).
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
        eapply exp_ext_no_mem_dep.
      }
      { econstructor. }

      simpl.
      rewrite /Sop.sem_add//=.
      rewrite /Sop.sem_binarith//=.
      rewrite /constrain_lb.
      rewrite -float_add_irf. repeat f_equal. rewrite IRF_IFR_inv //.
    }
    {
      apply eval_expr_fun_spec. rewrite /unconstrained_to_constrained_fun.
      edestruct (global_env_exp) as (expl&?&?).
      simpl.
      econstructor.
      { econstructor. }
      {
        assert ((Floats.Float.sub Floats.Float.zero (IRF a))
               = (IRF (- a))) as Heq.
        { rewrite -(IRF_IFR_inv (Floats.Float.zero)).
          rewrite float_sub_irf. f_equal. rewrite IFR_zero. nra.
        }
        econstructor.
        econstructor.
        eapply eval_Evar_global; eauto.
        { eapply deref_loc_reference; eauto. }
        { repeat econstructor. }
        { eauto. }
        2:{  eauto. }
        rewrite /exp_ef_external; reflexivity.
        rewrite ?Heq; eapply exp_ext_spec.
        rewrite ?Heq; eapply exp_ext_no_mem_dep.
      }
      simpl.
      rewrite /Sop.sem_sub//=.
      rewrite /Sop.sem_binarith//=.
      replace f with (IRF (IFR f)) at 1 by (apply IRF_IFR_inv).
      rewrite float_sub_irf. f_equal.
    }
    {
      apply eval_expr_fun_spec. rewrite /unconstrained_to_constrained_fun.
      edestruct (global_env_expit) as (expl&?&?).
      simpl.
      econstructor.
      { econstructor. }
      econstructor.
      { repeat econstructor. }
      {
        econstructor.
        econstructor.
        eapply eval_Evar_global; eauto.
        { eapply deref_loc_reference; eauto. }
        { repeat econstructor. }
        { eauto. }
        2:{  eauto. }
        rewrite /expit_ef_external; reflexivity.
        eapply expit_ext_spec.
        eapply expit_ext_no_mem_dep.
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
  }
  eapply IHx; eauto.
  { inversion Hnone; eauto. }
  { inversion Hin; subst. eauto. }
Qed.

Variable data : list Values.val.
Variable params : list R.

Let ge := globalenv prog.
Let tge := globalenv tprog.

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
                            found_parameters.

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
  destruct TRANSL as (params'&?&?&?&?).
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

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  ∃ f', Genv.find_funct tge v = Some f' /\ transf_fundef fpmap fcorrection f = OK f'.
Proof.
  intros. destruct TRANSL' as (Hmatch&Hrest).
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
  intros. destruct TRANSL' as (Hmatch&Hrest).
  eapply (Genv.find_funct_ptr_match) in Hmatch as (?&tfun&Htfun); eauto.
  intuition.
  eexists; split; eauto.
  inversion H2; eauto.
  rewrite /=. subst. rewrite H1 => //=.
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

Definition match_mem_locals en m0 m1 :=
  forall id l ty chunk ofs v,
    Maps.PTree.get id en = Some (l, ty) ->
    access_mode ty = Ctypes.By_value chunk ->
    Mem.loadv chunk m0 (Values.Vptr l ofs) = Some v ->
    Mem.loadv chunk m1 (Values.Vptr l ofs) = Some v.

Definition match_mem_globals m0 m1 :=
  forall id l ty chunk ofs v,
    Genv.find_symbol ge id = Some l ->
    access_mode ty = Ctypes.By_value chunk ->
    Mem.loadv chunk m0 (Values.Vptr l ofs) = Some v ->
    Genv.find_symbol tge id = Some l /\
    match fpmap id with
    | None =>
        Mem.loadv chunk m1 (Values.Vptr l ofs) = Some v
    | Some fe =>
        match ty with
        | Breal =>
            exists fl, Mem.loadv chunk m1 (Values.Vptr l ofs) = Some (Values.Vfloat fl) /\
                       (∀ en' m' t', eval_expr tge en' m' t' (fe (Econst_float fl Breal)) v)
        | _ => True
        end
    end.

Definition match_mem en m0 m1 :=
  match_mem_locals en m0 m1 /\
  match_mem_globals m0 m1.

Definition valid_env (en : env) :=
  forall id, Maps.PTree.get id en <> None -> fpmap id = None.

Lemma evaluation_preserved:
  forall en m0 m1 t,
    valid_env en ->
    match_mem en m0 m1 ->
      (forall e v, eval_expr ge en m0 t e v ->
                   forall e', transf_expr fpmap e = OK e' ->
                              eval_expr tge en m1 t e' v)
  /\  (forall el vl, eval_exprlist ge en m0 t el vl ->
                     forall el', transf_exprlist fpmap el = OK el' ->
                                 eval_exprlist tge en m1 t el' vl)
  /\  (forall e loc ofs s, eval_lvalue ge en m0 t e loc ofs s ->
                           match e with
                           | Eindexed e el ty =>
                               forall el', transf_exprlist fpmap el = OK el' ->
                                           eval_lvalue tge en m1 t (Eindexed e el' ty)
                                             loc ofs s
                           | _ => eval_lvalue tge en m1 t e loc ofs s
                           end).
Proof.
  intros en m0 m1 t Hval Hmatch.
  apply (eval_exprs_ind ge en m0 t); intros.
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
    monadInv H8.
    econstructor; eauto.
    eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
    intros ??. eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
  }
  { monadInv H. econstructor. }
  { monadInv H2. econstructor; eauto. erewrite typeof_transf_expr; eauto. }
  {
    inversion H; subst.
    { simpl in H2.
      rewrite Hval in H2; last by congruence.
      { inversion H2; subst. econstructor; eauto.
        inversion H1. subst.
        { econstructor; eauto.
          destruct Hmatch as (Hloc&Hglo).
          eapply Hloc; eauto.
        }
        { eapply deref_loc_reference; eauto. }
      }
    }
    { simpl in H2.
      destruct (fpmap id) as [fe|] eqn:Hfpe; last first.
      { inversion H2; subst. econstructor; eauto. admit. }
      destruct ty; try congruence.
      inversion H2; subst.
      admit.
    }
    { subst. admit. }
  }

  (* list *)
  { monadInv H. simpl. econstructor; eauto. }
  { monadInv H3. simpl. econstructor; eauto. }

  (* lvalue *)
  { simpl. econstructor; eauto. }
  { simpl. econstructor; eauto. rewrite symbols_preserved; auto. }

  { simpl. destruct ty => //=; try (econstructor; eauto). }
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
Admitted.

End PRESERVATION.

Global Instance TransfReparameterizationtLink : TransfLink match_prog.
Admitted.
