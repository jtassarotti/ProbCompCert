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
Require Import CStanCont.

Require Import String. 
Require Import Clightdefs. 
Import Clightdefs.ClightNotations.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Section SEMANTICS.

Variable ge: genv.

Inductive alloc_variables: env -> mem ->
                           list (ident * Ctypes.type) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof ge ty) = (m1, b1) ->
      alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, ty) :: vars) e2 m2.

Inductive bind_parameters (e: env):
                           mem -> list (ident * Ctypes.type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ge ty m b Ptrofs.zero Full v1 m1 ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

Fixpoint create_undef_temps (temps: list (ident * Ctypes.type)) : temp_env :=
  match temps with
  | nil => PTree.empty val
  | (id, t) :: temps' => PTree.set id Vundef (create_undef_temps temps')
 end.

Fixpoint bind_parameter_temps (formals: list (ident * Ctypes.type)) (args: list val)
                              (le: temp_env) : option temp_env :=
 match formals, args with
 | nil, nil => Some le
 | (id, t) :: xl, v :: vl => bind_parameter_temps xl vl (PTree.set id v le)
 | _, _ => None
 end.

Definition block_of_binding (id_b_ty: ident * (block * Ctypes.type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ge ty) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

Definition set_opttemp (optid: option ident) (v: val) (le: temp_env) :=
  match optid with
  | None => le
  | Some id => PTree.set id v le
  end.

Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
  match sl with
  | LSnil => sl
  | LScons None s sl' => sl
  | LScons (Some i) s sl' => select_switch_default sl'
  end.

Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
  match sl with
  | LSnil => None
  | LScons None s sl' => select_switch_case n sl'
  | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
  end.

Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
  match select_switch_case n sl with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

(** Turn a labeled statement into a sequence *)

Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
  match sl with
  | LSnil => Sskip
  | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
  end.

(** ** Evaluation of expressions *)

Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.
Locate deref_loc.

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
  | eval_Ecast:   forall a ty v1 v,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty m = Some v ->
      eval_expr (Ecast a ty) v
  | eval_Elvalue: forall a loc ofs bf v,
      eval_lvalue a loc ofs bf ->
      deref_loc (typeof a) m loc ofs bf v ->
      eval_expr a v

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

Definition Ederef' (a: expr) (t: type) : expr :=
  match a with
  | Eaddrof a' t' => if type_eq t (typeof a') then a' else Ederef a t
  | _ => Ederef a t
  end.


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

Inductive state: Type :=
  | State                               (**r execution of a statement *)
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (le: temp_env)
      (m: mem) : state

  (* | StanState *)
  (*     (f: function) *)
  (*     (s: statement) *)
  (*     (k: cont) *)
  (*     (e: env) *)
  (*     (le: temp_env) *)
  (*     (m: mem)  *)
  (*     (ta: float) : state (* ta is the running target *) *)

  | Callstate                           (**r calling a function *)
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem) : state
  | Returnstate                         (**r returning from a function *)
      (res: val)
      (k: cont)
      (m: mem) : state
.

(** Find the statement and manufacture the continuation
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: statement) (k: cont)
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 s2 =>
      match find_label lbl s1 (Kloop1 s1 s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 (Kloop2 s1 s2 k)
      end
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSnil => None
  | LScons _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

Inductive step: state -> trace -> state -> Prop :=
  | step_assign:   forall f a1 a2 k e le m loc ofs bf v2 v m',
      eval_lvalue e le m a1 loc ofs bf ->
      eval_expr e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs bf v m' ->
      step (State f (Sassign a1 a2) k e le m)
        E0 (State f Sskip k e le m')
  | step_set:   forall f id a k e le m v,
      eval_expr e le m a v ->
      step (State f (Sset id a) k e le m)
        E0 (State f Sskip k e (PTree.set id v le) m)
  | step_call:   forall f optid a al k e le m tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr e le m a vf ->
      eval_exprlist e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      step (State f (Scall optid a al) k e le m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)
  | step_builtin:   forall f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef tyargs al) k e le m)
         t (State f Sskip k e (set_opttemp optid vres le) m')
  | step_seq:  forall f s1 s2 k e le m,
      step (State f (Ssequence s1 s2) k e le m)
        E0 (State f s1 (Kseq s2 k) e le m)
  | step_skip_seq: forall f s k e le m,
      step (State f Sskip (Kseq s k) e le m)
        E0 (State f s k e le m)
  | step_continue_seq: forall f s k e le m,
      step (State f Scontinue (Kseq s k) e le m)
        E0 (State f Scontinue k e le m)
  | step_break_seq: forall f s k e le m,
      step (State f Sbreak (Kseq s k) e le m)
        E0 (State f Sbreak k e le m)
  | step_ifthenelse:  forall f a s1 s2 k e le m v1 b,
      eval_expr e le m a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      step (State f (Sifthenelse a s1 s2) k e le m)
        E0 (State f (if b then s1 else s2) k e le m)
  | step_loop: forall f s1 s2 k e le m,
      step (State f (Sloop s1 s2) k e le m)
        E0 (State f s1 (Kloop1 s1 s2 k) e le m)
  | step_skip_or_continue_loop1:  forall f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kloop1 s1 s2 k) e le m)
        E0 (State f s2 (Kloop2 s1 s2 k) e le m)
  | step_break_loop1:  forall f s1 s2 k e le m,
      step (State f Sbreak (Kloop1 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)
  | step_skip_loop2: forall f s1 s2 k e le m,
      step (State f Sskip (Kloop2 s1 s2 k) e le m)
        E0 (State f (Sloop s1 s2) k e le m)
  | step_break_loop2: forall f s1 s2 k e le m,
      step (State f Sbreak (Kloop2 s1 s2 k) e le m)
        E0 (State f Sskip k e le m)
  | step_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn None) k e le m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k e le m v v' m',
      eval_expr e le m a v ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le m)
        E0 (Returnstate v' (call_cont k) m')
  | step_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f Sskip k e le m)
        E0 (Returnstate Vundef k m')
  | step_skip_break_switch: forall f x k e le m,
      x = Sskip \/ x = Sbreak ->
      step (State f x (Kswitch k) e le m)
        E0 (State f Sskip k e le m)
  | step_continue_switch: forall f k e le m,
      step (State f Scontinue (Kswitch k) e le m)
        E0 (State f Scontinue k e le m)
  | step_internal_function: forall f vargs k m e le m1,
      function_entry f vargs m e le m1 ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e le m1)
  | step_external_function: forall ef targs tres cconv vargs k m vres t m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef targs tres cconv) vargs k m)
         t (Returnstate vres k m')
  | step_returnstate: forall v optid f e le k m,
      step (Returnstate v (Kcall optid f e le k) m)
        E0 (State f Sskip k e (set_opttemp optid v le) m)
  .
End SEMANTICS.

Inductive function_entry (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters ge e m1 f.(fn_params) vargs m' ->
      le = create_undef_temps f.(fn_temps) ->
      function_entry ge f vargs m e le m'.

Definition stepf (ge: genv) := step ge (function_entry ge).

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_data_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge $"main" = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p (Callstate f nil Kstop m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_data_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

Definition semantics (p: program) :=
  let ge := globalenv p in
  Semantics_gen stepf (initial_state p) final_state ge ge.
