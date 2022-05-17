Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.

Require Import CStan.
Require CStanSemanticsBackend.

Require Import String. 
Require Import Clightdefs. 
Import Clightdefs.ClightNotations.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Section SEMANTICS.

(**********************************************************************************************************)
Inductive block_state : Type :=
  | Model (ta : float) : block_state
  | Other : block_state.
(**********************************************************************************************************)


Variable ge: genv.

(** ** Evaluation of expressions *)

Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.
Variable bs : block_state.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Econst_single:   forall f ty,
      eval_expr (Econst_single f ty) (Vsingle f)
  | eval_Econst_long:   forall i ty,
      eval_expr (Econst_long i ty) (Vlong i)
  | eval_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_expr (Etempvar id ty) v
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation op v1 (typeof a) m = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
  | eval_Esizeof: forall ty1 ty,
      eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | eval_Ealignof: forall ty1 ty,
      eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
  | eval_Ecast: forall a ty v1 v,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty m = Some v ->
      eval_expr (Ecast a ty) v
  | eval_Elvalue: forall a loc ofs bf v,
      eval_lvalue a loc ofs bf ->
      deref_loc (typeof a) m loc ofs bf v ->
      eval_expr a v
  | eval_Etarget: forall ty ta,
      bs = Model ta ->
      eval_expr (Etarget ty) (Vfloat ta)
with eval_lvalue: expr -> block -> ptrofs -> bitfield -> Prop :=
  | eval_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue (Evar id ty) l Ptrofs.zero Full
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      eval_lvalue (Evar id ty) l Ptrofs.zero Full
  | eval_Ederef: forall a ty l ofs,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Ederef a ty) l ofs Full
  | eval_Efield_struct:   forall a i ty l ofs id co att delta bf,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tstruct id att ->
      ge.(genv_cenv)!id = Some co ->
      field_offset ge i (co_members co) = OK (delta, bf) ->
      eval_lvalue (Efield a i ty) l (Ptrofs.add ofs (Ptrofs.repr delta)) bf.

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
(*
Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.
*)

Inductive eval_exprlist: list expr -> typelist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil Tnil nil
  | eval_Econs:   forall a bl ty tyl v1 v2 vl,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty m = Some v2 ->
      eval_exprlist bl tyl vl ->
      eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

End EXPR.

(** ** Transition semantics for statements and functions *)

(** Pop continuation until a call or stop *)

Inductive cont: Type :=
  | Kstop: cont
  | Kseq: statement -> cont -> cont       (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kloop1: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s1] in [Sloop s1 s2] *)
  | Kloop2: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s2] in [Sloop s1 s2] *)
  | Kswitch: cont -> cont       (**r catches [break] statements arising out of [switch] *)
  | Kcall: option ident ->                  (**r where to store result *)
           function ->                      (**r calling function *)
           env ->                           (**r local env of calling function *)
           temp_env ->                      (**r temporary env of calling function *)
           block_state ->                   (**r block state of calling function *)
           cont -> cont.

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kloop1 s1 s2 k => call_cont k
  | Kloop2 s1 s2 k => call_cont k
  | Kswitch k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ _ => True
  | _ => False
  end.

Inductive state: Type :=
  | State                             (**r execution of statements *)
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (le: temp_env)
      (m: mem)
      (ta: block_state) : state
  | Callstate                           (**r calling a function *)
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem)
  | Returnstate                         (**r returning from a function *)
      (res: val)
      (k: cont)
      (m: mem)
      (ta: block_state) : state.

Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

Inductive step: state -> trace -> state -> Prop :=
  | step_assign:   forall f a1 a2 k e le m ta loc ofs bf v2 v m',
      eval_lvalue e le m ta a1 loc ofs bf ->
      eval_expr e le m ta a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs bf v m' ->
      step (State f (Sassign a1 a2) k e le m ta)
                 E0 (State f Sskip k e le m' ta)
  | step_set:   forall f id a k e le m ta v,
      eval_expr e le m ta a v ->
      step (State f (Sset id a) k e le m ta)
        E0 (State f Sskip k e (PTree.set id v le) m ta)
  | step_call:   forall f optid a al k e le m ta tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr e le m ta a vf ->
      eval_exprlist e le m ta al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      step (State f (Scall optid a al) k e le m ta)
        E0 (Callstate fd vargs (Kcall optid f e le ta k) m)
  | step_builtin:   forall f optid ef tyargs al k e le m ta vargs t vres m',
      eval_exprlist e le m ta al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef tyargs al) k e le m ta)
         t (State f Sskip k e (CStanSemanticsBackend.set_opttemp optid vres le) m' ta)
  | step_seq:  forall f s1 s2 k e le m ta,
      step (State f (Ssequence s1 s2) k e le m ta)
        E0 (State f s1 (Kseq s2 k) e le m ta)
  | step_skip_seq: forall f s k e le m ta,
      step (State f Sskip (Kseq s k) e le m ta)
        E0 (State f s k e le m ta)
  | step_continue_seq: forall f s k e le m ta,
      step (State f Scontinue (Kseq s k) e le m ta)
        E0 (State f Scontinue k e le m ta)
  | step_break_seq: forall f s k e le m ta,
      step (State f Sbreak (Kseq s k) e le m ta)
        E0 (State f Sbreak k e le m ta)
  | step_ifthenelse:  forall f a s1 s2 k e le m ta v1 b,
      eval_expr e le m ta a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      step (State f (Sifthenelse a s1 s2) k e le m ta)
        E0 (State f (if b then s1 else s2) k e le m ta)
  | step_loop: forall f s1 s2 k e le m ta,
      step (State f (Sloop s1 s2) k e le m ta)
        E0 (State f s1 (Kloop1 s1 s2 k) e le m ta)
  | step_skip_or_continue_loop1:  forall f s1 s2 k e le m x ta,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kloop1 s1 s2 k) e le m ta)
        E0 (State f s2 (Kloop2 s1 s2 k) e le m ta)
  | step_break_loop1:  forall f s1 s2 k e le m ta,
      step (State f Sbreak (Kloop1 s1 s2 k) e le m ta)
        E0 (State f Sskip k e le m ta)
  | step_skip_loop2: forall f s1 s2 k e le m ta,
      step (State f Sskip (Kloop2 s1 s2 k) e le m ta)
        E0 (State f (Sloop s1 s2) k e le m ta)
  | step_break_loop2: forall f s1 s2 k e le m ta,
      step (State f Sbreak (Kloop2 s1 s2 k) e le m ta)
        E0 (State f Sskip k e le m ta)
  | step_return_0: forall f k e le m m' ta,
      f.(fn_blocktype) <> CStan.BTModel ->
      Mem.free_list m (CStanSemanticsBackend.blocks_of_env ge e) = Some m' ->
      step (State f (Sreturn None) k e le m ta)
        E0 (Returnstate Vundef (call_cont k) m' ta)
  | step_return_1: forall f a k e le m ta v v' m',
      f.(fn_blocktype) <> CStan.BTModel ->
      eval_expr e le m ta a v ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' ->
      Mem.free_list m (CStanSemanticsBackend.blocks_of_env ge e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le m ta)
        E0 (Returnstate v' (call_cont k) m' ta)
  | step_skip_call: forall f k e le m m' ta,
      is_call_cont k ->
      f.(fn_blocktype) <> CStan.BTModel ->
      Mem.free_list m (CStanSemanticsBackend.blocks_of_env ge e) = Some m' ->
      step (State f Sskip k e le m ta)
        E0 (Returnstate Vundef k m' ta)
  | step_skip_call_model: forall f k e le m m' bs v,
      is_call_cont k ->
      f.(fn_blocktype) = CStan.BTModel ->
      bs = Model v ->
      Mem.free_list m (CStanSemanticsBackend.blocks_of_env ge e) = Some m' ->
      step (State f Sskip k e le m bs)
        E0 (Returnstate (Vfloat v) k m' Other)

  | step_skip_break_switch: forall f x k e le m ta,
      x = Sskip \/ x = Sbreak ->
      step (State f x (Kswitch k) e le m ta)
        E0 (State f Sskip k e le m ta)
  | step_continue_switch: forall f k e le m ta,
      step (State f Scontinue (Kswitch k) e le m ta)
        E0 (State f Scontinue k e le m ta)
  (* | step_internal_function: forall f vargs k m e le m1 ta, *)
  (*     function_entry f vargs m e le m1 -> *)
  (*     step (Callstate (Internal f) vargs k m ta) *)
  (*       E0 (State f f.(fn_body) k e le m1 ta) *)

  | step_internal_function: forall f vargs k m e le m1,
      function_entry f vargs m e le m1 ->
      f.(fn_blocktype) <> CStan.BTModel ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e le m1 Other)

  | step_internal_function_model: forall f vargs k m e le m1,
      function_entry f vargs m e le m1 ->
      f.(fn_blocktype) = CStan.BTModel ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e le m1 (Model (Float.of_int (Int.repr  0))))

  | step_external_function: forall ef targs tres cconv vargs k m vres t m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef targs tres cconv) vargs k m)
         t (Returnstate vres k m' Other)
  | step_returnstate: forall v optid f e le k m ta_caller ta,
      step (Returnstate v (Kcall optid f e le ta_caller k) m ta)
        E0 (State f Sskip k e (CStanSemanticsBackend.set_opttemp optid v le) m ta_caller)

  | step_target: forall f a k e le m bs ta v ta' attr,
      eval_expr e le m bs a v ->
      bs = Model ta ->
      v = Vfloat ta' ->
      (* TODO: WARNING: should we assume it's a Tfloat 64? Or do we need to handle casting? *)
      typeof a = Tfloat F64 attr ->
      step (State f (Starget a) k e le m bs)
        E0 (State f Sskip k e le m (Model (Float.add ta ta')))
  .
End SEMANTICS.

Inductive function_entry (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      CStanSemanticsBackend.alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      CStanSemanticsBackend.bind_parameters ge e m1 f.(fn_params) vargs m' ->
      le = CStanSemanticsBackend.create_undef_temps f.(fn_temps) ->
      function_entry ge f vargs m e le m'.

Definition stepf (ge: genv) := step ge (function_entry ge).

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_data_intro: forall b f m0 ,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge $"main" = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p (Callstate f nil Kstop m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_data_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m Other) r.

Definition semantics (p: program) :=
  let ge := globalenv p in
  Semantics_gen stepf (initial_state p) final_state ge ge.
