Require Import Coqlib.
Require Import Smallstep.
Require Import Sbackend.
Require Import CStan.
Require Import Clight.
Require Import Ssemantics.
Require Import Errors.
Require Import Globalenvs.
Require Import Memory.
Require Import Maps.
Require Import Values.
Require Import Linking Ctypes.
Import Integers.
Require CStanSemanticsBackend.
Require CStanCont.

Require Import String.
Open Scope string_scope.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Local Open Scope clight_scope.



Section PRESERVATION.

Variable prog: CStan.program.
Variable tprog: Clight.program.
Let ge := CStan.globalenv prog.
Let tge := Clight.globalenv tprog.

(** Matching continuations *)
Inductive match_cont : CStanCont.cont -> Clight.cont -> Prop :=
  | match_Kstop:
      match_cont CStanCont.Kstop Clight.Kstop
  | match_Kseq: forall s k ts tk ,
      transf_statement s = OK ts ->
      match_cont k tk ->
      match_cont (CStanCont.Kseq s k) (Clight.Kseq ts tk)
  | match_Kloop1: forall s1 s2 k ts1 ts2 tk ,
      transf_statement s1 = OK ts1 ->
      transf_statement s2 = OK ts2 ->
      match_cont k tk ->
      match_cont (CStanCont.Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk)
  | match_Kloop2: forall s1 s2 k ts1 ts2 tk ,
      transf_statement s1 = OK ts1 ->
      transf_statement s2 = OK ts2 ->
      match_cont k tk ->
      match_cont (CStanCont.Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk)
  | match_Kswitch: forall k tk ,
      match_cont k tk ->
      match_cont (CStanCont.Kswitch k) (Kswitch tk)
  | match_Kcall: forall optid fn e le k tfn tk ,
      transf_function fn = OK tfn ->
      match_cont k tk ->
      match_cont (CStanCont.Kcall optid fn e le k)
                        (Kcall optid tfn e le tk). 

Inductive match_states: CStanSemanticsBackend.state -> Clight.state -> Prop :=
  | match_regular_states:
      forall f s k e le m tf ts tk
      (TRF: transf_function f = OK tf)
      (TRS: transf_statement s = OK ts)
      (MCONT: match_cont k tk),
      match_states (CStanSemanticsBackend.State f s k e le m)
                   (Clight.State tf ts tk e le m)
  | match_call_state:
      forall fd vargs k m tfd tk
      (TRFD: Sbackend.transf_fundef fd = OK tfd)
      (MCONT: match_cont k tk),
      match_states (CStanSemanticsBackend.Callstate fd vargs k m)
                   (Clight.Callstate tfd vargs tk m) 
  | match_return_state:
      forall v k m tk
      (MCONT: match_cont k tk),
      match_states (CStanSemanticsBackend.Returnstate v k m)
                   (Clight.Returnstate v tk m).

(** * Relational specification of the transformation *)

Definition match_prog (p: CStan.program) (tp: Clight.program) :=
    match_program (fun ctx f tf => Sbackend.transf_fundef f = OK tf) eq p tp
 /\ prog_types tp = CStan.prog_types p.

Variable TRANSL: match_prog prog tprog.

Lemma comp_env_preserved:
  genv_cenv tge = CStan.genv_cenv ge.
Proof.
  unfold tge, ge. destruct TRANSL as [_ EQ].
  generalize (prog_comp_env_eq tprog).
  generalize (CStan.prog_comp_env_eq prog).
  destruct tprog, prog; simpl in *.
  congruence.
Qed.

Inductive tr_function: CStan.function -> Clight.function -> Prop :=
  | tr_function_intro: forall f tf,
      (* tr_stmt f.(CStan.fn_body) tf.(fn_body) -> *)
      fn_return tf = CStan.fn_return f ->
      fn_callconv tf = CStan.fn_callconv f ->
      fn_params tf = CStan.fn_params f ->
      fn_vars tf = CStan.fn_vars f ->
      tr_function f tf.

Inductive tr_fundef: CStan.fundef -> Clight.fundef -> Prop :=
  | tr_internal: forall f tf,
      tr_function f tf ->
      tr_fundef (Internal f) (Internal tf)
  | tr_external: forall ef targs tres cconv,
      tr_fundef (External ef targs tres cconv) (External ef targs tres cconv).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  apply (Genv.senv_match (proj1 TRANSL)).
Qed.

Lemma symbols_preserved:
  forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  apply (Genv.find_symbol_match (proj1 TRANSL)).
Qed.

Lemma functions_translated:
  forall (v: val) (f: CStan.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ Sbackend.transf_fundef f = OK tf.
Proof.
  intros.
  edestruct (Genv.find_funct_match (proj1 TRANSL)) as (ctx' & tf & A & B & C'); eauto.
Qed.

Lemma type_of_fundef_preserved:
  forall fd tfd,
  Sbackend.transf_fundef fd = OK tfd -> type_of_fundef tfd = CStan.type_of_fundef fd.
Proof.
  intros. destruct fd; monadInv H; auto.
  monadInv EQ. simpl; unfold type_of_function; simpl. auto.
Qed.

Lemma sizeof_equiv :
  forall t,
  sizeof ge t = sizeof tge t.
Proof.
  rewrite comp_env_preserved.
  auto.
Qed.

Lemma alignof_equiv :
  forall t,
  alignof ge t = alignof tge t.
Proof.
  rewrite comp_env_preserved.
  auto.
Qed.

Lemma transf_types_eq :
  forall e te,
  transf_expression e = OK te -> CStan.typeof e = Clight.typeof te.
Proof.
  intro e.
  induction e; intros; inv H;
    (* base cases *)
    try (simpl in *; reflexivity);

    (* cases with inductive hypothesis: Ederef, Eunop, Ebinop *)
    try (monadInv H1;  (* invert our inductive transf_expression *)
         constructor). (* the rest of the proof follows precisely by constructor *)
Qed.

Lemma eval_expr_correct:
  forall e le m a v ta
  (TRE: transf_expression a = OK ta),
  CStanSemanticsBackend.eval_expr ge e le m a v -> Clight.eval_expr tge e le m ta v.
Proof.
  intros e le m a.
  induction a; intros; simpl in TRE; monadInv TRE; simpl.

  (* Econst expressions: *)
  - (* inversion identifies the eval_Econst_* and eval_lvalue as possibilities *)
    inv H. (* apply inversion on our CStan.eval_expr *)
    constructor. (* for eval_Econst_*, apply the corresponding constructor *)
    inv H0.      (* for eval_lvalue, inversion on the new hypothesis shows that the pattern is invalid *)
  - inv H. constructor. inv H0.
  - inv H. constructor. inv H0.
  - inv H; try constructor; inv H0.

  - (* Evar expressions *)
    inv H. (* apply inversion on our CStan.eval_expr, this matches eval_lvalue. *)
    eapply Clight.eval_Elvalue.

    2:{
    inv H1; simpl in *.
    eapply Clight.deref_loc_value; eauto.
    eapply Clight.deref_loc_reference; eauto.
    eapply Clight.deref_loc_copy; eauto.
    eapply Clight.deref_loc_bitfield; eauto.
    }

    inv H0.
    eapply Clight.eval_Evar_local. eauto.
    eapply Clight.eval_Evar_global; eauto.
    rewrite symbols_preserved. eauto.

  - (* Etempvar expressions *)
    inv H.
    constructor. eauto. inv H0.

  (* Inductive-hypotheses *)

  - (* Ederef expressions *)
    inv H.
    inv H0.
    eapply Clight.eval_Elvalue.
    eapply Clight.eval_Ederef; eauto.
    simpl in *.
    destruct H1.
    eapply Clight.deref_loc_value; eauto.
    eapply Clight.deref_loc_reference; eauto.
    eapply Clight.deref_loc_copy; eauto.
    eapply Clight.deref_loc_bitfield; eauto.

  - (* cast *)
    inv H.
    econstructor; eauto.
    rewrite (transf_types_eq a x) in H4; eauto.
    inv H0.

  - (* field struct *)
    inv H.

    {
      inv H0.
      simpl in *.
      eapply Clight.eval_Elvalue.
      eapply Clight.eval_Efield_struct; eauto.
      rewrite (transf_types_eq a x) in H5; eauto.
      assert (SUB: CStan.prog_comp_env prog = ge); eauto; rewrite SUB in *.
      rewrite comp_env_preserved in *; eauto.
      assert (SUB: CStan.prog_comp_env prog = ge); eauto; rewrite SUB in *.
      rewrite comp_env_preserved in *; eauto.
      destruct H1.
      eapply Clight.deref_loc_value; eauto.
      eapply Clight.deref_loc_reference; eauto.
      eapply Clight.deref_loc_copy; eauto.
      eapply Clight.deref_loc_bitfield; eauto.
    }

  - (* addrof *)
    inv H.
    inv H0.

  - (* Eunop expressions *)
    inv H.                               (* invert with CStan.eval_Eunop -- we must additionally show CStan.eval_lvalue is invalid. *)
    econstructor.                        (* apply Clight.eval_Eunop -- we must additionally show Cop.sem_unary_operation *)
    apply (IHa v1 x EQ H4).       (* Eunop is then shown to be valid by inductive case of it's argument *)
    rewrite (transf_types_eq a x) in H5; eauto. (* Cop.sem_unary_operation is true by transf_types_eq, so long as EQ *)
    inv H0.                                     (* CStan.eval_lvalue is invalid. *)

  - (* Ebinop expressions *)
    inv H.                                 (* invert with CStan.eval_Ebinop *)
    2: inv H0.                       (* this also pattern-matches on the invalid CStan.eval_lvalue -- just deal with that now. *)
    econstructor.                          (* apply Clight.eval_Ebinop *)
    apply (IHa1 v1 x EQ H5).        (* The first argument is then proven true by the first inductive case*)
    apply (IHa2 v2 x0 EQ1 H6).      (* The second argument is then proven true by the second inductive case*)

    rewrite (transf_types_eq a1 x ) in H7. (* we additionally need to show that Cop.sem_binary_operation is true. *)
    rewrite (transf_types_eq a2 x0) in H7.
    rewrite comp_env_preserved.
    eauto.
    eauto.
    eauto.

  (* Two more base cases *)

  - (* Esizeof expressions *)
    inv H.
    rewrite sizeof_equiv.
    apply Clight.eval_Esizeof.
    inv H0.

  - (* Ealignof expressions *)
    inv H.
    rewrite alignof_equiv.
    apply Clight.eval_Ealignof.
    inv H0.
Qed.

Lemma eval_lvalue_correct:
  forall e le m a b ofs bf ta
  (TRE: transf_expression a = OK ta),
  CStanSemanticsBackend.eval_lvalue ge e le m a b ofs bf -> Clight.eval_lvalue tge e le m ta b ofs bf.
Proof.
  intros e le m a.
  induction a; intros; monadInv TRE; try (inv H).
  - eapply Clight.eval_Evar_local; eauto.
  - eapply Clight.eval_Evar_global; eauto.
    rewrite symbols_preserved; auto.
  - eapply Clight.eval_Ederef.
    eapply eval_expr_correct; eauto.
  - eapply eval_Efield_struct.
    eapply eval_expr_correct; eauto.
    rewrite (transf_types_eq a x) in *; eauto.
    rewrite comp_env_preserved in *; eauto.
    rewrite comp_env_preserved in *; eauto.
Qed.

Lemma types_correct:
  forall e x, transf_expression e = OK x -> CStan.typeof e = Clight.typeof x.
Proof.
  intro e.
  induction e; intros; simpl in *; monadInv H; simpl; trivial.
Qed.

Lemma match_cont_call_cont:
  forall k tk ,
  match_cont k tk  ->
  match_cont (CStanCont.call_cont k) (call_cont tk) .
Proof.
  induction 1; simpl; auto; intros; econstructor; eauto.
Qed.

Lemma blocks_of_env_preserved:
  forall e, blocks_of_env tge e = CStanSemanticsBackend.blocks_of_env ge e.
Proof.
  intros; unfold blocks_of_env, CStanSemanticsBackend.blocks_of_env.
  unfold block_of_binding, CStanSemanticsBackend.block_of_binding.
  rewrite comp_env_preserved. auto.
Qed.

Lemma transf_sem_cast_inject:
  forall f tf x tx v v' m,
  transf_expression x = OK tx ->
  transf_function f = OK tf ->
  Cop.sem_cast v (CStan.typeof x) (CStan.fn_return f) m = Some v' ->
  Cop.sem_cast v (Clight.typeof tx) (fn_return tf) m = Some v'.
Proof.
  intros.
  generalize (types_correct _ _ H); intro.
  monadInv H0. simpl in *.
  rewrite <- H2.
  auto.
Qed.

Lemma alloc_variables_preserved:
  forall e m params e' m',
  CStanSemanticsBackend.alloc_variables ge e m params e' m' ->
  Clight.alloc_variables tge e m params e' m'.
Proof.
  induction 1; econstructor; eauto. rewrite comp_env_preserved; auto.
Qed.

Lemma bind_parameters_preserved:
  forall e m params args m',
  CStanSemanticsBackend.bind_parameters ge e m params args m' ->
  bind_parameters tge e m params args m'.
Proof.
  induction 1; econstructor; eauto. inv H0.
- eapply Clight.assign_loc_value; eauto.
- eapply Clight.assign_loc_copy; eauto; rewrite <- comp_env_preserved in *; auto.
Qed.

Lemma eval_exprlist_correct_simple:
  forall env le es tes tys m vs
  (TREL: transf_expression_list es = OK tes)
  (EVEL: CStanSemanticsBackend.eval_exprlist ge env le m es tys vs),
  Clight.eval_exprlist tge env le m tes tys vs.
Proof.
  intros env le es.
  induction es; intros.
  monadInv TREL.
  inv EVEL; eauto.
  econstructor.
  monadInv TREL.
  inv EVEL; eauto.
  econstructor; eauto.
  eapply eval_expr_correct; eauto.
  generalize (types_correct _ _ EQ); intro.
  rewrite <- H; eauto.
Qed.

Lemma step_simulation:
  forall S1 t S2, CStanSemanticsBackend.stepf ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus Clight.step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1. simpl; intros; inv MS; simpl in *; try (monadInv TRS).

  - (* assign *)
    exists (Clight.State tf Clight.Sskip tk e le m').
    split.
    eapply plus_one.
    generalize (types_correct _ _ EQ); intro.
    generalize (types_correct _ _ EQ1); intro.
    rewrite H3 in *.
    rewrite H4 in *.
    unfold step1.
    eapply Clight.step_assign; eauto.
    eapply eval_lvalue_correct; eauto.
    eapply eval_expr_correct; eauto.
    * inv H2.
      ** eapply Clight.assign_loc_value; eauto.
      ** eapply Clight.assign_loc_copy; try (rewrite comp_env_preserved); eauto.
      ** eapply Clight.assign_loc_bitfield; eauto.
    * eapply match_regular_states; eauto.
  - (* set *)
    intros; inv MS.
    econstructor.
    monadInv TRS.
    split. eapply plus_one. unfold step1.
    econstructor.
    eapply eval_expr_correct; eauto.
    eapply match_regular_states; eauto.

  - (* call *)
    intros; inv MS.
    monadInv TRS.
    exploit eval_expr_correct; eauto; intro.
    exploit eval_exprlist_correct_simple; eauto. intro tvargs.
    exploit functions_translated; eauto. intros [tfd [P Q]].
    econstructor. split. eapply plus_one. eapply step_call with (fd := tfd).
    generalize (types_correct _ _ EQ); intro TYA. rewrite<-TYA. eauto.
    eauto. eauto. eauto.
    rewrite (type_of_fundef_preserved fd); eauto.
    eapply match_call_state; eauto.
    econstructor; eauto.

  - (* builtin *)
    intros; inv MS.
    monadInv TRS.
    exists (Clight.State tf Sskip tk e (set_opttemp optid vres le) m').
    split. eapply plus_one. unfold step1.
    eapply step_builtin.
    eapply eval_exprlist_correct_simple; eauto.
    eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
    eapply match_regular_states; eauto.
  - (* sequence seq *)
    intros.
    inv MS; monadInv TRS.
    exists (Clight.State tf x (Clight.Kseq x0 tk) e le m).
    split.
    eapply plus_one.
    unfold step1.
    eapply Clight.step_seq.
    eapply match_regular_states; eauto.
    econstructor; eauto.
  - (* skip sequence *)
    intros.
    inv MS; monadInv TRS.
    inv MCONT.
    exists (Clight.State tf ts tk0 e le m).
    split.
    eapply plus_one.
    unfold step1.
    eapply Clight.step_skip_seq.
    eapply match_regular_states; eauto.
  - (* continue sequence *)
    intros; inv MS; monadInv TRS.
    inv MCONT.
    exists (Clight.State tf Scontinue tk0 e le m).
    split.
    eapply plus_one.
    unfold step1.
    eapply step_continue_seq.
    eapply match_regular_states; eauto.
  - (* break sequence *)
    intros; inv MS; monadInv TRS.
    inv MCONT.
    exists (Clight.State tf Sbreak tk0 e le m).
    split.
    eapply plus_one; unfold step1.
    eapply step_break_seq.
    eapply match_regular_states; eauto.
  - (* if then else *)
    intros; inv MS; monadInv TRS.
    econstructor.
    split.
    eapply plus_one; unfold step1.
    econstructor.
    eapply eval_expr_correct; eauto.
    generalize (types_correct _ _ EQ); intro.
    rewrite <- H1; eauto.
    eapply match_regular_states; eauto.
    destruct b; eauto.
  - (* step_loop *)
    intros; inv MS; monadInv TRS.
    exists (Clight.State tf x (Kloop1 x x0 tk) e le m).
    split.
    eapply plus_one; unfold step1.
    eapply step_loop.
    eapply match_regular_states; eauto.
    eapply match_Kloop1; eauto.
  - (* step_skip_or_continue_loop1 *)
    intros. inv MS; inv MCONT; destruct H;
    repeat (
      econstructor; split;
      try (eapply plus_one; unfold step1;
        eapply step_skip_or_continue_loop1;
        monadInv TRF; monadInv TRS; eauto);
      eapply match_regular_states; eauto; eapply match_Kloop2; eauto
    ).

  - (* step_break_loop1 *)
    intros; inv MS; monadInv TRS; inv MCONT.
    econstructor. split.
    eapply plus_one; unfold step1.
    eapply step_break_loop1; eauto.
    eapply match_regular_states; eauto.
  - (* step_skip_loop2 *)
    intros; inv MS; monadInv TRS; inv MCONT.
    exists (Clight.State tf (Sloop ts1 ts2) tk0 e le m).
    split.
    eapply plus_one; unfold step1.
    eapply step_skip_loop2.
    eapply match_regular_states; eauto.
    simpl. rewrite H2. rewrite H4. auto.

  - (* step_break_loop2 *)
    intros; inv MS; monadInv TRS; inv MCONT.
    exists (Clight.State tf Sskip tk0 e le m).
    split. eapply plus_one; unfold step1.
    eapply  step_break_loop2.
    eapply match_regular_states; eauto.

  - (* step_return_0 *)
    intros; inv MS; monadInv TRS.
    exists (Returnstate Values.Vundef (call_cont tk) m').
    split. eapply plus_one; unfold step1.
    eapply step_return_0; eauto. rewrite blocks_of_env_preserved. eauto.
    eapply match_return_state; eauto.
    eapply match_cont_call_cont; eauto.
  - (* step_return_1 *)
    intros; inv MS.
    exists (Returnstate v' (call_cont tk) m').
    monadInv TRS.
    split. eapply plus_one; unfold step1.
    econstructor; eauto.
    eapply eval_expr_correct; eauto.
    eapply transf_sem_cast_inject; eauto.
    rewrite blocks_of_env_preserved. eauto.
    eapply match_return_state; eauto.
    eapply match_cont_call_cont; eauto.

  - (* step_skip_call *)
    intros; inv MS; monadInv TRS.
    econstructor.
    split. eapply plus_one; unfold step1.
    econstructor.
    unfold CStanCont.is_call_cont in H.
    assert (is_call_cont tk). inv MCONT; simpl in *; auto. auto.
    rewrite blocks_of_env_preserved. eauto.
    eapply match_return_state; eauto.

  - (* step_skip_break_switch *)
    intros; inv MS. inv MCONT.
    econstructor.
    split. eapply plus_one; unfold step1.
    econstructor.
    destruct H; simpl in *.
    monadInv TRF; monadInv TRS; eauto.
    monadInv TRF; monadInv TRS; eauto.
    eapply match_regular_states; eauto.

  - (* step_continue_switch *)
    intros; inv MS; monadInv TRS; inv MCONT.
    exists (Clight.State tf Scontinue tk0 e le m).
    split. eapply plus_one; unfold step1.
    econstructor.
    eapply match_regular_states; eauto.

  - (* step_internal_function *)
    intros; inv MS.
    monadInv TRFD.
    exists (Clight.State x x.(fn_body) tk e le m1).
    split. eapply plus_one; unfold step1.
    eapply step_internal_function.
    inversion H.
    assert (tr_function f x).
      intros; monadInv EQ.
      econstructor; eauto.
    inv H4.
    econstructor; try (rewrite H7); try (rewrite H8); eauto.
    eapply alloc_variables_preserved; eauto.
    eapply bind_parameters_preserved; eauto.
    monadInv EQ; eauto.
    eapply match_regular_states; eauto.
    monadInv EQ. eauto.

  - (* step_external_function *)
    intros. inv MS.
    monadInv TRFD.
    exists (Returnstate vres tk m').
    split. eapply plus_one. eapply step_external_function. eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
    eapply match_return_state; eauto.
  - (* step_returnstate *)
    intros. inv MS.
    inv MCONT.
    exists (Clight.State tfn Sskip tk0 e (set_opttemp optid v le) m).
    split. apply plus_one. eapply step_returnstate.
    eapply match_regular_states; eauto.
Qed.

Lemma function_ptr_translated:
  forall m0
    (b: block) (f: CStan.fundef)
  (H0 : Genv.init_mem prog = Some m0)
  (H1 : Genv.find_symbol ge $"main" = Some b)
  (H2 : Genv.find_funct_ptr ge b = Some f)
  (H3 : CStan.type_of_fundef f = Tfunction Tnil type_int32s AST.cc_default)
  , Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ Sbackend.transf_fundef f = OK tf.
Proof.
  intros.
  edestruct (Genv.find_funct_ptr_match (proj1 TRANSL)) as (ctx' & tf & A & B & C'); eauto.
Qed.

Lemma initial_states_simulation:
  forall S, CStanSemanticsBackend.initial_state prog S ->
  exists R, Clight.initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (tf & A & B).
  exists (Clight.Callstate tf nil Clight.Kstop m0).
  split.
  eapply Clight.initial_state_intro; eauto.
  erewrite <- (Genv.init_mem_match (proj1 TRANSL)); eauto.
  replace (prog_main tprog) with $"main".
  rewrite <- H1. apply symbols_preserved.
  generalize (match_program_main (proj1 TRANSL)).
  unfold AST.prog_main.
  unfold CStan.program_of_program.
  simpl; eauto.
  exploit type_of_fundef_preserved; eauto.
  intro FDTY. rewrite FDTY; eauto.
  econstructor; eauto.
  eapply match_Kstop.
Qed.

Lemma final_states_simulation:
  forall S R r,
  match_states S R -> CStanSemanticsBackend.final_state S r -> Clight.final_state R r.
Proof.
  intros. inv H0. inv H. inv MCONT. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (CStanSemanticsBackend.semantics prog) (Clight.semantics1 tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact initial_states_simulation.
  eexact final_states_simulation.
  eexact step_simulation.
Qed.

End PRESERVATION.
