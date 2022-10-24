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

Lemma typeof_correction_fold_plus fe l typ i :
  (∀ e, typeof e = Breal -> typeof (fe e) = Breal) ->
  typeof (fold_right (fun ofs e => Ebinop (fe (Eindexed (Evar i typ)
                                                (Econs (Econst_int ofs Bint) Enil) Breal)) Stanlight.Plus e Breal)
        (Econst_float Floats.Float.zero Breal)
        l) = Breal.
Proof.
  intros Hfe.
  induction l => //=.
Qed.

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

Lemma check_nodup_params_spec ids res :
  check_nodup_params ids = OK res ->
  NoDup ids.
Proof.
  rewrite /check_nodup_params.
  destruct (nodupb _ _) eqn:Heq; inversion 1.
  clear -Heq. induction ids.
  { econstructor. }
  { simpl in Heq. destruct (in_dec _ _ _); first inversion Heq.
    econstructor; auto.
  }
Qed.

Lemma found_parameters_irrel {A B} id b1 (oe1 : A) b2 (oe2 : B) id1' v1 oe1' id2' v2 oe2' defs :
  find_parameter defs (id, b1, oe1) = OK (id1', v1, oe1') ->
  find_parameter defs (id, b2, oe2) = OK (id2', v2, oe2') ->
  id1' = id2' /\ v1 = v2.
Proof.
  induction defs.
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

Lemma In_flatten_parameter_list_id' prs id b ofs :
  In (id, b, ofs) (flatten_parameter_list prs) ->
  In id (map (fun '(id, _ ,_) => id) prs).
Proof.
  induction prs.
  - inversion 1.
  - destruct a as ((?&[])&?) => //=;
    try (destruct 1 as [Hleft|Hright]; [ left; congruence | right; eauto ]).
    rewrite /flatten_parameter_list/=.
    intros [Hleft|Hright]%in_app_or.
    { rewrite /parameter_basic_to_list/data_basic_to_list/= in Hleft.
      apply in_combine_l in Hleft. apply repeat_spec in Hleft. left; congruence. }
    { right. eauto. }
Qed.

Lemma In_flatten_parameter_list_id pr id b ofs :
  In (id, b, ofs) (flatten_parameter_list (pr_parameters_vars pr)) ->
  In id (pr_parameters_ids pr).
Proof. eapply In_flatten_parameter_list_id'. Qed.


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

Lemma count_down_ofs_len n : length (count_down_ofs n) = n.
Proof.
  induction n => //=.
  rewrite IHn //.
Qed.

Lemma count_up_ofs_len n : length (count_up_ofs n) = n.
Proof.
  rewrite /count_up_ofs rev_length count_down_ofs_len //.
Qed.

Lemma eval_const_float tge en m pm t v v0 :
  eval_expr tge en m pm t (Econst_float v Breal) v0 ->
  v0 = Values.Vfloat v.
Proof.
  { intros Heval. inv Heval; try (inv H; done); eauto. }
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


Let lower_upper_correction_expr :=
      (fun a b x =>
              let a := Econst_float a Breal in
              let b := Econst_float b Breal in
              let one := Econst_float (Floats.Float.of_int Integers.Int.one) Breal in
              let call := Ecall (Evar $"expit" (Bfunction (Bcons Breal Bnil) Breal)) (Econs x Enil) Breal in
              let pre_log := (Ebinop (Ebinop b Minus a Breal) Times
                                (Ebinop call Times (Ebinop one Minus call Breal) Breal) Breal) in
              Ecall (Evar $"log" (Bfunction (Bcons Breal Bnil) Breal)) (Econs pre_log Enil) Breal).

Lemma eval_correction_lower_upper tge e m pm t a b xpr r 
  (MATH: genv_has_mathlib tge)
  (VE2 : env_no_shadow_mathlib e)
  (PARAM_NOSHADOW: param_mem_no_shadow_mathlib pm) :
  eval_expr tge e m pm t xpr (Values.Vfloat (IRF r)) ->
  eval_expr tge e m pm t
            (lower_upper_correction_expr a b xpr)
           (Values.Vfloat (IRF (log_deriv_constrain_fn (Clower_upper a b) r))).
Proof.
  simpl.
  edestruct MATH as (_&(expit&Hfe&Hfuncte)&(log&Hfl&Hfunctl)).
  intros Hexpr.
  econstructor. 
  {
    eapply eval_Elvalue.
    eapply eval_Evar_global; eauto.
    { rewrite /env_no_shadow_mathlib in VE2.
      inversion VE2 as [|??? Hnoshadow'].
      inversion Hnoshadow' as [|??? Hnoshadow''].
      inversion Hnoshadow'' as [|??? Hnoshadow'''].
      eauto.
    }
    {
      inversion PARAM_NOSHADOW as [|??? Hnoshadow'].
      inversion Hnoshadow' as [|??? Hnoshadow''].
      inversion Hnoshadow'' as [|??? Hnoshadow'''].
      eauto.
    }
    { eapply deref_loc_reference; eauto. }
  }
  { econstructor; last by econstructor.
    { 
      econstructor.
      { repeat econstructor. }
      {  econstructor.  econstructor.
         { eapply eval_Elvalue.
           eapply eval_Evar_global; eauto.
           { rewrite /env_no_shadow_mathlib in VE2.
             inversion VE2 as [|??? Hnoshadow'].
             inversion Hnoshadow' as [|??? Hnoshadow''].
             inversion Hnoshadow'' as [|??? Hnoshadow'''].
             eauto.
           }
           {
             inversion PARAM_NOSHADOW as [|??? Hnoshadow'].
             inversion Hnoshadow' as [|??? Hnoshadow''].
             inversion Hnoshadow'' as [|??? Hnoshadow'''].
             eauto.
           }
           { eapply deref_loc_reference; eauto. }
         }
         { econstructor. eauto. econstructor. }
         { eauto. }
         { eauto. }
         { rewrite //=. }
         eapply expit_ext_spec.
         econstructor.
         { repeat econstructor. }
         { econstructor.
           eapply eval_Elvalue.
           eapply eval_Evar_global; eauto.
           { rewrite /env_no_shadow_mathlib in VE2.
             inversion VE2 as [|??? Hnoshadow'].
             inversion Hnoshadow' as [|??? Hnoshadow''].
             inversion Hnoshadow'' as [|??? Hnoshadow'''].
             eauto.
           }
           {
             inversion PARAM_NOSHADOW as [|??? Hnoshadow'].
             inversion Hnoshadow' as [|??? Hnoshadow''].
             inversion Hnoshadow'' as [|??? Hnoshadow'''].
             eauto.
           }
           { eapply deref_loc_reference; eauto. }
           { econstructor. eauto. econstructor. }
           { eauto. }
           { eauto. }
           { rewrite //=. }
           eapply expit_ext_spec.
         }
      rewrite //=.
      rewrite //=.
    }
    rewrite //=.
  }
  }
  eauto.
  eauto.
  rewrite //=.
  eapply log_ext_spec''.
  { f_equal. f_equal. rewrite /deriv_constrain_lb_ub.
    rewrite ?float_mul_irf'.
    rewrite ?float_sub_irf'.
    rewrite ?IFR_IRF_inv.
    rewrite ?float_sub_irf'.
    rewrite ?IFR_one.
    nra.
  }
Qed.
