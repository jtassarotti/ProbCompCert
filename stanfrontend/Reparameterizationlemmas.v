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

Lemma vars_check_shadow_ok id b xt:
  vars_check_shadow (id, b) = OK xt ->
  ¬ In id math_idents.
Proof.
  intros Hin.
  unfold vars_check_shadow in Hin.
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
  edestruct MATH as [ _ (expit&Hfe&Hfuncte) (log&Hfl&Hfunctl)].
  intros Hexpr.
  econstructor. 
  {
    eapply eval_Eglvalue.
    eapply eval_Evar_global; eauto.
    {
      inversion PARAM_NOSHADOW as [|??? Hnoshadow'].
      inversion Hnoshadow' as [|??? Hnoshadow''].
      inversion Hnoshadow'' as [|??? Hnoshadow'''].
      eauto.
    }
    { rewrite /env_no_shadow_mathlib in VE2.
      inversion VE2 as [|??? Hnoshadow'].
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
         { eapply eval_Eglvalue.
           eapply eval_Evar_global; eauto.
           {
             inversion PARAM_NOSHADOW as [|??? Hnoshadow'].
             inversion Hnoshadow' as [|??? Hnoshadow''].
             inversion Hnoshadow'' as [|??? Hnoshadow'''].
             eauto.
           }
           { rewrite /env_no_shadow_mathlib in VE2.
             inversion VE2 as [|??? Hnoshadow'].
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
           eapply eval_Eglvalue.
           eapply eval_Evar_global; eauto.
           {
             inversion PARAM_NOSHADOW as [|??? Hnoshadow'].
             inversion Hnoshadow' as [|??? Hnoshadow''].
             inversion Hnoshadow'' as [|??? Hnoshadow'''].
             eauto.
           }
           { rewrite /env_no_shadow_mathlib in VE2.
             inversion VE2 as [|??? Hnoshadow'].
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

Lemma count_up_ofs_aux_range1 st n ofs' :
  (Z.of_nat (st + n) <= Integers.Ptrofs.modulus ->
   In ofs' (count_up_ofs_aux st n) ->
   Z.of_nat st <= Integers.Ptrofs.intval ofs')%Z.
Proof.
  revert st.
  induction n => st.
  { simpl. intros Hlt Hin. exfalso; eauto. }
  { simpl. intros Hlt [Hleft|Hright].
    { subst.
      specialize Integers.Ptrofs.unsigned_repr.
      rewrite /Integers.Ptrofs.unsigned.
      intros ->; try lia.
      split; try lia. rewrite /Integers.Ptrofs.max_unsigned; lia.
    }
    specialize (IHn (S st)).
    etransitivity; last eapply IHn; try lia; eauto.
  }
Qed.

Definition env_no_shadow_param {A} (en : env) (pm : ParamMap.param_mem A) :=
  forall id, ParamMap.is_id_alloc pm id = true -> ParamMap.is_id_alloc en id = false.

Definition wf_type (b: basic) :=
  match b with
  | Barray _ z => (-1 < z /\ z < Integers.Int.modulus - 1 /\ z < Integers.Ptrofs.modulus - 1)%Z
  | _ => True
  end.

Lemma flat_nodups_cons_inv {A} x (l2 : list (AST.ident * A * _)) :
  flat_nodups (x :: l2)%list ->
  flat_nodups l2.
Proof. inversion 1; eauto. Qed.

Lemma flat_nodups_app_tail_inv {A} (l1 l2 : list (AST.ident * A * _)) :
  flat_nodups (l1 ++ l2)%list ->
  flat_nodups l2.
Proof.
  induction l1.
  - simpl. auto.
  - simpl. intros ?%flat_nodups_cons_inv; auto.
Qed.

Lemma assign_global_params_nodups_get i b ofs bs pm0 v vs pm :
  assign_global_params ((i, b, ofs) :: bs) pm0 (Values.Vfloat v :: vs) pm ->
  flat_nodups (((i, b, ofs) :: bs)) ->
  is_id_alloc pm i = true /\ get pm i (Integers.Ptrofs.intval ofs) = Some v.
Proof.
  intros Hassign Hnin.
  exploit (assign_global_params_tail_not_in); eauto.
  { inv Hnin; eauto. }
  intros. split; auto.
  eapply gs_is_alloc; eauto.
Qed.

Lemma typeof_collect_corrections {A} (l : list (_ * _ * A)) :
  typeof (collect_corrections l) = Breal.
Proof.
  induction l as [|((?&v)&?) ?]; eauto => //=.
  rewrite /change_of_variable_correction.
  rewrite /change_of_variable_correction_fun.
  destruct (vd_constraint v), (vd_type v) => //=; destruct b => //=.
Qed.

Lemma eval_correction e m pm t found_parameters tge
  (MATH: genv_has_mathlib tge)
  (ENOSHADOW : env_no_shadow_param e pm)
  (VE : env_no_shadow_mathlib e)
  (PARAM_NOSHADOW: param_mem_no_shadow_mathlib pm) :
  ∀ (ups : list R) (pm0 : param_mem _),
    flat_nodups
      (concat (map parameter_basic_to_list (map (λ '(id, v, fe), (id, vd_type v, fe)) found_parameters)))
    → Forall (λ '(_, b, _), wf_type b) (map (λ '(id, v, fe), (id, vd_type v, fe)) found_parameters)
      → assign_global_params
          (concat (map parameter_basic_to_list (map (λ '(id, v, fe), (id, vd_type v, fe)) found_parameters))) pm0
          (map R2val ups) pm
        → eval_expr tge e m pm t (collect_corrections found_parameters)
            (Values.Vfloat
               (IRF
                  (list_plus
                     (list_apply
                        (map log_deriv_constrain_fn
                           (map (λ '(_, v, _), vd_constraint v) (concat (map variable_to_list found_parameters))))
                        (map val2R (map R2val ups)))))).
Proof.
  induction (found_parameters).
  { rewrite //=. intros ups pm0 Hnodups Hsize.
    inversion 1; subst.
    rewrite IRF_0. econstructor. }
  { intros ups pm0 Hnodups Hsize.
    destruct a as ((?&?)&?).
    rewrite /=/change_of_variable_correction/=.
    destruct (vd_constraint v) eqn:Hvd.
    (* CIdentity *)
    { rewrite /=.
      rewrite map_app.
      destruct (vd_type v).
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=. rewrite Rplus_0_l. destruct ups; inv H6.
        eapply IHl; eauto.
        { simpl in Hnodups. eapply flat_nodups_app_tail_inv in Hnodups; eauto. }
        { inv Hsize; eauto. }
      }
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=. rewrite Rplus_0_l. destruct ups; inv H6.
        eapply IHl; eauto.
        { simpl in Hnodups. eapply flat_nodups_app_tail_inv in Hnodups; eauto. }
        { inv Hsize; eauto. }
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
        { simpl in Hnodups.
          eapply flat_nodups_app_tail_inv in Hnodups; eauto. }
        { inv Hsize; eauto. }
        rewrite Hups2. eauto.
      }
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=. rewrite Rplus_0_l. destruct ups; inv H6.
        eapply IHl; eauto.
        { simpl in Hnodups. eapply flat_nodups_app_tail_inv in Hnodups; eauto. }
        { inv Hsize; eauto. }
      }
    }
    (* Clower *)
    { rewrite /=.
      rewrite map_app.
      simpl in Hnodups.
      destruct (vd_type v) eqn:Hvdty.
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=.
        rewrite -H6 in H.
        destruct ups as [|? ups]; inv H6.
        exploit (assign_global_params_nodups_get); eauto.
        intros (?&?).
        econstructor. 
        eapply eval_Eplvalue.
        econstructor.
        { eapply ENOSHADOW; auto. }
        { eauto. }
        eapply (IHl ups); eauto.
        { simpl in Hnodups. inv Hnodups; eauto. }
        { inv Hsize; eauto. }
        simpl.
        rewrite ln_exp. 
        rewrite typeof_collect_corrections /=.
        rewrite /Sop.sem_add//=.
        rewrite /Sop.sem_binarith//=.
        rewrite float_add_irf IFR_IRF_inv //.
      }
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=.
        rewrite -H6 in H.
        destruct ups as [|? ups]; inv H6.
        exploit (assign_global_params_nodups_get); eauto.
        intros (?&?).
        econstructor. 
        eapply eval_Eplvalue.
        econstructor.
        { eapply ENOSHADOW; auto. }
        { eauto. }
        eapply (IHl ups); eauto.
        { simpl in Hnodups. inv Hnodups; eauto. }
        { inv Hsize; eauto. }
        simpl.
        rewrite ln_exp. 
        rewrite typeof_collect_corrections /=.
        rewrite /Sop.sem_add//=.
        rewrite /Sop.sem_binarith//=.
        rewrite float_add_irf IFR_IRF_inv //.
      }
      2:{
        rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=.
        rewrite -H6 in H.
        destruct ups as [|? ups]; inv H6.
        exploit (assign_global_params_nodups_get); eauto.
        intros (?&?).
        econstructor. 
        eapply eval_Eplvalue.
        econstructor.
        { eapply ENOSHADOW; auto. }
        { eauto. }
        eapply (IHl ups); eauto.
        { simpl in Hnodups. inv Hnodups; eauto. }
        { inv Hsize; eauto. }
        simpl.
        rewrite ln_exp. 
        rewrite typeof_collect_corrections /=.
        rewrite /Sop.sem_add//=.
        rewrite /Sop.sem_binarith//=.
        rewrite float_add_irf IFR_IRF_inv //.
      }
      {
        intros Hassign.
        exploit assign_global_params_app_inv; eauto. intros (pm'&vs1&vs2&Heq1&Hlen&Hassign1&Hassign2).
        apply map_eq_app in Heq1 as (ups1&ups2&Heq_ups&Hups1&Hups2).
        rewrite Heq_ups. rewrite ?map_app.
        rewrite list_apply_app; last first.
        { rewrite Hups1. rewrite ?map_length.
          rewrite repeat_length.
          rewrite Hlen length_array_basic_to_list1 //.
        }
        rewrite list_plus_app.

        eapply (eval_Ebinop _ _ _ _ _ _ _ _ _
                  ((Values.Vfloat (IRF (list_plus
                                          (list_apply
                                             (map log_deriv_constrain_fn
                                                (map (λ '(_, v0, _), vd_constraint v0)
                                                   (repeat (i, {| vd_type := b; vd_constraint := Clower f |}, o) (Z.to_nat z))))
                                             (map val2R (map R2val ups1)))))))).
        {
          clear Hassign2 Hassign2.
          move:Hnodups Hassign Hlen.
          rewrite /parameter_basic_to_list/data_basic_to_list/=.
          rewrite count_up_ofs_equiv.
          rewrite count_up_int_equiv.
          inv Hsize. unfold wf_type in H1.
          rewrite Hvdty in H1.
          assert (Z.of_nat (S O) + (Z.of_nat (Z.to_nat z)) < Integers.Ptrofs.modulus /\
                    Z.of_nat (S O) + (Z.of_nat (Z.to_nat z)) < Integers.Int.modulus
                 )%Z as Hsize'.
          { lia. }
          move: Hsize'.

        generalize 0%nat as st.
        clear Hassign1.
        revert pm0 ups1.
        induction (Z.to_nat z).
        { simpl. intros st Hnodups Hassign Hlen. rewrite IRF_0. econstructor. }
        {
          intros pm0 ups1 st Hsize. simpl.
          simpl. intros Hnodups Hassign Hlen.
          subst.
          destruct ups1 as [| u ups1].
          { exfalso. simpl in Hlen. lia. }
          simpl in Hassign.
          exploit (assign_global_params_nodups_get); eauto.
          intros (?&?).
          econstructor.
          { eapply eval_Eplvalue.
            econstructor.
            { repeat econstructor; eauto. }
            { eapply ENOSHADOW; auto. }
            rewrite /Integers.Ptrofs.of_int.
            rewrite Integers.Int.unsigned_repr; eauto.
            {  clear -Hsize. split; first lia.
               move: Hsize.
               rewrite /Integers.Int.max_unsigned.
               lia. }
          }
          eapply IHn.
          { lia. }
          { inv Hnodups; eauto. }
          { inv Hassign; eauto. }
          { simpl in Hlen. lia. }

          rewrite (typeof_correction_fold_plus (λ x, x)) //=.
          rewrite /Sop.sem_add//=.
          rewrite /Sop.sem_binarith//=.
          rewrite ln_exp. rewrite float_add_irf'.
          simpl.
          rewrite ?IFR_IRF_inv //.
        }
      }
      { eapply IHl.  eauto.
        { simpl in Hnodups.
          eapply flat_nodups_app_tail_inv in Hnodups; eauto. }
        { inv Hsize; eauto. }
        { erewrite Hups2; eauto. }
      }
      rewrite (typeof_correction_fold_plus (λ x, x)) //=.
      rewrite typeof_collect_corrections /=.
      rewrite /Sop.sem_add//=.
      rewrite /Sop.sem_binarith//=.
      rewrite float_add_irf'.
      repeat f_equal; rewrite ?IFR_IRF_inv; eauto.
      }
    }
    (* Cupper *)
    { rewrite /=.
      rewrite map_app.
      simpl in Hnodups.
      destruct (vd_type v) eqn:Hvdty.
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=.
        rewrite -H6 in H.
        destruct ups as [|? ups]; inv H6.
        exploit (assign_global_params_nodups_get); eauto.
        intros (?&?).
        econstructor. 
        { econstructor. econstructor.
          eapply eval_Eplvalue.
          econstructor.
          { eapply ENOSHADOW; auto. }
          { eauto. }
          rewrite //=. }
        eapply (IHl ups); eauto.
        { simpl in Hnodups. inv Hnodups; eauto. }
        { inv Hsize; eauto. }
        simpl.
        rewrite ln_exp. 
        rewrite typeof_collect_corrections /=.
        rewrite /Sop.sem_add//=.
        rewrite /Sop.sem_binarith//=.
        rewrite float_sub_irf'.
        rewrite float_add_irf' IFR_IRF_inv //.
        rewrite -IRF_0. rewrite ?IFR_IRF_inv. do 3 f_equal. rewrite /list_apply. nra.
      }
      { rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=.
        rewrite -H6 in H.
        destruct ups as [|? ups]; inv H6.
        exploit (assign_global_params_nodups_get); eauto.
        intros (?&?).
        econstructor. 
        { econstructor. econstructor.
          eapply eval_Eplvalue.
          econstructor.
          { eapply ENOSHADOW; auto. }
          { eauto. }
          rewrite //=. }
        eapply (IHl ups); eauto.
        { simpl in Hnodups. inv Hnodups; eauto. }
        { inv Hsize; eauto. }
        simpl.
        rewrite ln_exp. 
        rewrite typeof_collect_corrections /=.
        rewrite /Sop.sem_add//=.
        rewrite /Sop.sem_binarith//=.
        rewrite float_sub_irf'.
        rewrite float_add_irf' IFR_IRF_inv //.
        rewrite -IRF_0. rewrite ?IFR_IRF_inv. do 3 f_equal. rewrite /list_apply. nra.
      }
      2:{
        rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=.
        rewrite -H6 in H.
        destruct ups as [|? ups]; inv H6.
        exploit (assign_global_params_nodups_get); eauto.
        intros (?&?).
        econstructor. 
        { econstructor. econstructor.
          eapply eval_Eplvalue.
          econstructor.
          { eapply ENOSHADOW; auto. }
          { eauto. }
          rewrite //=. }
        eapply (IHl ups); eauto.
        { simpl in Hnodups. inv Hnodups; eauto. }
        { inv Hsize; eauto. }
        simpl.
        rewrite ln_exp. 
        rewrite typeof_collect_corrections /=.
        rewrite /Sop.sem_add//=.
        rewrite /Sop.sem_binarith//=.
        rewrite float_sub_irf'.
        rewrite float_add_irf' IFR_IRF_inv //.
        rewrite -IRF_0. rewrite ?IFR_IRF_inv. do 3 f_equal. rewrite /list_apply. nra.
      }
      {
        intros Hassign.
        exploit assign_global_params_app_inv; eauto. intros (pm'&vs1&vs2&Heq1&Hlen&Hassign1&Hassign2).
        apply map_eq_app in Heq1 as (ups1&ups2&Heq_ups&Hups1&Hups2).
        rewrite Heq_ups. rewrite ?map_app.
        rewrite list_apply_app; last first.
        { rewrite Hups1. rewrite ?map_length.
          rewrite repeat_length.
          rewrite Hlen length_array_basic_to_list1 //.
        }
        rewrite list_plus_app.

        eapply (eval_Ebinop _ _ _ _ _ _ _ _ _
                  ((Values.Vfloat (IRF (list_plus
                                          (list_apply
                                             (map log_deriv_constrain_fn
                                                (map (λ '(_, v0, _), vd_constraint v0)
                                                   (repeat (i, {| vd_type := b; vd_constraint := Cupper f |}, o) (Z.to_nat z))))
                                             (map val2R (map R2val ups1)))))))).
        {
          clear Hassign2 Hassign2.
          move:Hnodups Hassign Hlen.
          rewrite /parameter_basic_to_list/data_basic_to_list/=.
          rewrite count_up_ofs_equiv.
          rewrite count_up_int_equiv.
          inv Hsize. unfold wf_type in H1.
          rewrite Hvdty in H1.
          assert (Z.of_nat (S O) + (Z.of_nat (Z.to_nat z)) < Integers.Ptrofs.modulus /\
                    Z.of_nat (S O) + (Z.of_nat (Z.to_nat z)) < Integers.Int.modulus
                 )%Z as Hsize'.
          { lia. }
          move: Hsize'.

        generalize 0%nat as st.
        clear Hassign1.
        revert pm0 ups1.
        induction (Z.to_nat z).
        { simpl. intros st Hnodups Hassign Hlen. rewrite IRF_0. econstructor. }
        {
          intros pm0 ups1 st Hsize. simpl.
          simpl. intros Hnodups Hassign Hlen.
          subst.
          destruct ups1 as [| u ups1].
          { exfalso. simpl in Hlen. lia. }
          simpl in Hassign.
          exploit (assign_global_params_nodups_get); eauto.
          intros (?&?).
          econstructor.
          { econstructor.
            { econstructor. }
            { eapply eval_Eplvalue. 
              econstructor.
              { repeat econstructor. }
              { eapply ENOSHADOW; auto. }
            rewrite /Integers.Ptrofs.of_int.
            rewrite Integers.Int.unsigned_repr; eauto.
            {  clear -Hsize. split; first lia.
               move: Hsize.
               rewrite /Integers.Int.max_unsigned.
               lia. }
            }
            { rewrite //=. }
          }
          eapply IHn.
          { lia. }
          { inv Hnodups; eauto. }
          { inv Hassign; eauto. }
          { simpl in Hlen. lia. }

          rewrite (typeof_correction_fold_plus
                     (λ x, (Ebinop (Econst_float Floats.Float.zero Breal) Minus x Breal))) //=.
          rewrite /Sop.sem_add//=.
          rewrite /Sop.sem_binarith//=.
          rewrite ln_exp.
        rewrite float_sub_irf'.
        rewrite float_add_irf' IFR_IRF_inv //.
        rewrite -IRF_0. rewrite ?IFR_IRF_inv. do 3 f_equal. rewrite /list_apply. nra.
        }
      }
      { eapply IHl.  eauto.
        { simpl in Hnodups.
          eapply flat_nodups_app_tail_inv in Hnodups; eauto. }
        { inv Hsize; eauto. }
        { erewrite Hups2; eauto. }
      }
      rewrite (typeof_correction_fold_plus (λ x, (Ebinop (Econst_float Floats.Float.zero Breal) Minus x Breal))) //=.
      rewrite typeof_collect_corrections /=.
      rewrite /Sop.sem_add//=.
      rewrite /Sop.sem_binarith//=.
      rewrite float_add_irf'.
      repeat f_equal; rewrite ?IFR_IRF_inv; eauto.
    }
    (* Clower_upper *)
    }
    { rewrite /=.
      rewrite map_app.
      simpl in Hnodups.
      destruct (vd_type v) eqn:Hvdty.
      {
        rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=.
        rewrite -H6 in H.
        destruct ups as [|? ups]; inv H6.
        exploit (assign_global_params_nodups_get); eauto.
        intros (?&?).
        econstructor.
        { eapply eval_correction_lower_upper; auto.
          eapply eval_Eplvalue.
          econstructor; eauto.
          { eapply ENOSHADOW; auto. }
          eauto.
        }
        eapply (IHl ups); eauto.
        { simpl in Hnodups. inv Hnodups; eauto. }
        { inv Hsize; eauto. }
        simpl.
        rewrite typeof_collect_corrections /=.
        rewrite /Sop.sem_add//=.
        rewrite /Sop.sem_binarith//=.
        rewrite float_add_irf' IFR_IRF_inv //.
        rewrite ?IFR_IRF_inv. do 3 f_equal.
      }
      {
        rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=.
        rewrite -H6 in H.
        destruct ups as [|? ups]; inv H6.
        exploit (assign_global_params_nodups_get); eauto.
        intros (?&?).
        econstructor.
        { eapply eval_correction_lower_upper; auto.
          eapply eval_Eplvalue.
          econstructor; eauto.
          { eapply ENOSHADOW; auto. }
          eauto.
        }
        eapply (IHl ups); eauto.
        { simpl in Hnodups. inv Hnodups; eauto. }
        { inv Hsize; eauto. }
        simpl.
        rewrite typeof_collect_corrections /=.
        rewrite /Sop.sem_add//=.
        rewrite /Sop.sem_binarith//=.
        rewrite float_add_irf' IFR_IRF_inv //.
        rewrite ?IFR_IRF_inv. do 3 f_equal.
      }
      2:{
        rewrite /=.
        inversion 1. subst.
        simpl.
        rewrite Hvd /=.
        rewrite -H6 in H.
        destruct ups as [|? ups]; inv H6.
        exploit (assign_global_params_nodups_get); eauto.
        intros (?&?).
        econstructor.
        { eapply eval_correction_lower_upper; auto. eapply eval_Eplvalue.
          econstructor; eauto.
          { eapply ENOSHADOW; auto. }
          eauto.
        }
        eapply (IHl ups); eauto.
        { simpl in Hnodups. inv Hnodups; eauto. }
        { inv Hsize; eauto. }
        simpl.
        rewrite typeof_collect_corrections /=.
        rewrite /Sop.sem_add//=.
        rewrite /Sop.sem_binarith//=.
        rewrite float_add_irf' IFR_IRF_inv //.
        rewrite ?IFR_IRF_inv. do 3 f_equal.
      }
      {
        intros Hassign.
        exploit assign_global_params_app_inv; eauto. intros (pm'&vs1&vs2&Heq1&Hlen&Hassign1&Hassign2).
        apply map_eq_app in Heq1 as (ups1&ups2&Heq_ups&Hups1&Hups2).
        rewrite Heq_ups. rewrite ?map_app.
        rewrite list_apply_app; last first.
        { rewrite Hups1. rewrite ?map_length.
          rewrite repeat_length.
          rewrite Hlen length_array_basic_to_list1 //.
        }
        rewrite list_plus_app.

        eapply (eval_Ebinop _ _ _ _ _ _ _ _ _
                  ((Values.Vfloat (IRF (list_plus
                                          (list_apply
                                             (map log_deriv_constrain_fn
                                                (map (λ '(_, v0, _), vd_constraint v0)
                                                   (repeat (i, {| vd_type := b; vd_constraint := Clower_upper f f0 |}, o) (Z.to_nat z))))
                                             (map val2R (map R2val ups1)))))))).
        {
          clear Hassign2 Hassign2.
          move:Hnodups Hassign Hlen.
          rewrite /parameter_basic_to_list/data_basic_to_list/=.
          rewrite count_up_ofs_equiv.
          rewrite count_up_int_equiv.
          inv Hsize. unfold wf_type in H1.
          rewrite Hvdty in H1.
          assert (Z.of_nat (S O) + (Z.of_nat (Z.to_nat z)) < Integers.Ptrofs.modulus /\
                    Z.of_nat (S O) + (Z.of_nat (Z.to_nat z)) < Integers.Int.modulus
                 )%Z as Hsize'.
          { lia. }
          move: Hsize'.

        generalize 0%nat as st.
        clear Hassign1.
        revert pm0 ups1.
        induction (Z.to_nat z).
        { simpl. intros st Hnodups Hassign Hlen. rewrite IRF_0. econstructor. }
        {
          intros pm0 ups1 st Hsize. simpl.
          simpl. intros Hnodups Hassign Hlen.
          subst.
          destruct ups1 as [| u ups1].
          { exfalso. simpl in Hlen. lia. }
          simpl in Hassign.
          exploit (assign_global_params_nodups_get); eauto.
          intros (?&?).
          econstructor.
          { eapply eval_correction_lower_upper; auto.
            eapply eval_Eplvalue.
            econstructor.
            { repeat econstructor. }
            { eapply ENOSHADOW; auto. }
            rewrite /Integers.Ptrofs.of_int.
            rewrite Integers.Int.unsigned_repr; eauto.
            {  clear -Hsize. split; first lia.
               move: Hsize.
               rewrite /Integers.Int.max_unsigned.
               lia. }
            }
          eapply IHn.
          { lia. }
          { inv Hnodups; eauto. }
          { inv Hassign; eauto. }
          { simpl in Hlen. lia. }

          rewrite /=.

          match goal with
          | [ |- context [transf_type ?a]] => assert (a = Breal) as ->
          end.
          { induction (count_up_int_aux _ _) => //=. }

          rewrite /Sop.sem_add//=.
          rewrite /Sop.sem_binarith//=.
        rewrite float_add_irf' IFR_IRF_inv //.
        rewrite ?IFR_IRF_inv. do 3 f_equal.
        }
      }
      { eapply IHl.  eauto.
        { simpl in Hnodups.
          eapply flat_nodups_app_tail_inv in Hnodups; eauto. }
        { inv Hsize; eauto. }
        { erewrite Hups2; eauto. }
      }
      match goal with
      | [ |- context [transf_type ?a]] => assert (a = Breal) as ->
      end.
      { induction (count_up_int _) => //=. }
      rewrite typeof_collect_corrections /=.
      rewrite /Sop.sem_add//=.
      rewrite /Sop.sem_binarith//=.
      rewrite float_add_irf'.
      repeat f_equal; rewrite ?IFR_IRF_inv; eauto.
      }
   } }
Qed.
