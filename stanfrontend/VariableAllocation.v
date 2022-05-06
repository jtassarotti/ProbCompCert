Require Import List.
Require Import Cop.
Require Import Ctypes.
Require Import CStan.
Require Import Errors.
Require Import String.
Require Import Floats.
Open Scope string_scope.
Require Import Coqlib.
Require Import Sops.
Require Import Cop.
Require Import Globalenvs.
Require Import Integers.
Require Import Clightdefs.
Require AST.
Require SimplExpr.
Require Import Constraints.

(* FIXME how do I share this notation? *)
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Notation "'do' X <~ A ; B" := (SimplExpr.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition tdouble := Tfloat F64 noattr.
Definition float_one := Floats.Float.of_int Int.one.
Definition float_zero := Floats.Float.of_int Int.zero.

Notation mon := SimplExpr.mon.
Notation ret := SimplExpr.ret.
Notation error := SimplExpr.error.
Notation gensym := SimplExpr.gensym.

Fixpoint mon_mmap {A B : Type} (f: A -> mon B) (l: list A) {struct l} : mon (list B) :=
  match l with
  | nil => ret nil
  | hd :: tl =>
    do hd' <~ f hd;
    do tl' <~ mon_mmap f tl;
    ret (hd' :: tl')
  end.

Definition option_mon_mmap {X Y:Type} (f: X -> mon Y) (ox: option X) : mon (option Y) :=
  match ox with
  | None => ret None
  | Some x => do x <~ f x; ret (Some x)
  end.

Definition as_fieldp (_Struct:AST.ident) (ref:AST.ident) (var:AST.ident) (fieldTy:Ctypes.type) : CStan.expr :=
  (Efield
    (Ederef
      (Evar ref (tptr (Tstruct _Struct noattr)))
      (Tstruct _Struct noattr))
    var fieldTy).

Definition as_field (_Struct:AST.ident) (_ref:AST.ident) (_var:AST.ident) (_fieldTy:Ctypes.type) : CStan.expr :=
  (Efield (Evar _ref (Tstruct _Struct noattr)) _var _fieldTy).

Fixpoint in_list (ps:list AST.ident) (i:AST.ident) : bool :=
  match ps with
  | nil => false
  | pi::ps => if Pos.eqb i pi then true else in_list ps i
  end.

Record struct_fns : Type := {
  is_member : AST.ident->bool;
  transl : AST.ident->type->expr;
}.

Fixpoint transf_expr (res:struct_fns) (e: CStan.expr) : mon CStan.expr :=
  match e with
  | CStan.Econst_int i t => ret (CStan.Econst_int i t)
  | CStan.Econst_float f t => ret (CStan.Econst_float f t)
  | CStan.Econst_single f t => ret (CStan.Econst_single f t)
  | CStan.Econst_long i t => ret (CStan.Econst_long i t)
  | CStan.Evar i t => ret (
    if res.(is_member) i
    then res.(transl) i t
    else Evar i t)
  | CStan.Etempvar i t => ret (CStan.Etempvar i t)
  | CStan.Ederef e t =>
      do e <~ transf_expr res e;
      ret (CStan.Ederef e t)
  | CStan.Ecast e t =>
      do e <~ transf_expr res e;
      ret (CStan.Ecast e t)
  | CStan.Eaddrof e t =>
      do e <~ transf_expr res e;
      ret (CStan.Eaddrof e t)
  | CStan.Efield e i t =>
      do e <~ transf_expr res e;
      ret (CStan.Efield e i t)
  | CStan.Eunop uop e t =>
      do e <~ transf_expr res e;
      ret (CStan.Eunop uop e t)
  | CStan.Ebinop bop e0 e1 t =>
      do e0 <~ transf_expr res e0;
      do e1 <~ transf_expr res e1;
      ret (CStan.Ebinop bop e0 e1 t)
  | CStan.Esizeof t0 t1 => ret (CStan.Esizeof t0 t1)
  | CStan.Ealignof t0 t1 => ret (CStan.Ealignof t0 t1)
  | CStan.Etarget t => ret (CStan.Etarget t)
end.

Fixpoint transf_statement (res:struct_fns) (s: CStan.statement) {struct s}: mon CStan.statement :=
match s with
  | Sskip => ret Sskip
  | Sassign e0 e1 =>
    do e0 <~ transf_expr res e0;
    do e1 <~ transf_expr res e1;
    ret (Sassign e0 e1)
  | Sset i e =>
    do e <~ transf_expr res e;
    ret (Sset i e)

  | Scall oi e le =>
    do e <~ transf_expr res e;
    do le <~ mon_mmap (transf_expr res) le;
    ret (Scall oi e le)

  | Sbuiltin oi ef lt le => error (msg "ret (Sbuiltin oi ef lt le)")

  | Ssequence s0 s1 =>
    do s0 <~ transf_statement res s0;
    do s1 <~ transf_statement res s1;
    ret (Ssequence s0 s1)

  | Sifthenelse e s0 s1 =>
    do s0 <~ transf_statement res s0;
    do s1 <~ transf_statement res s1;
    ret (Sifthenelse e s0 s1)

  | Sloop s0 s1 =>
    do s0 <~ transf_statement res s0;
    do s1 <~ transf_statement res s1;
    ret (Sloop s0 s1)

  | Sbreak => ret Sbreak

  | Scontinue => ret Scontinue

  | Sreturn oe =>
    do oe <~ option_mon_mmap (transf_expr res) oe;
    ret (Sreturn oe)

  | Starget e =>
    do e <~ transf_expr res e;
    ret (Starget e)

  | Stilde e d le (oe0, oe1) =>
    error (msg "DNE at this stage of pipeline")
end.

Definition init_unconstrained (p: program) : mon (AST.ident * statement) :=
  Constraints.callmath p MFInitUnconstrained nil.

Fixpoint over_fields
         (f : AST.ident * Ctypes.type -> statement)
         (body:statement)
         (fields: list (AST.ident * Ctypes.type))
  : statement :=
  match fields with
  | nil => body
  | struct_field::rest =>
    over_fields f (Ssequence (f struct_field) body) rest
  end.

Definition init_params (params : CStan.reserved_params) (perturb: AST.ident * statement) (struct_field : AST.ident * Ctypes.type): statement :=
  let (i, t)        := struct_field in
  let (x, call)     := perturb in
  let state_field   := as_field params.(res_params_type) params.(res_params_global_state) i t in
  Sassign state_field (Evar x t).


Definition adjust_proposal (params : CStan.reserved_params) (perturb: AST.ident * statement) (struct_field : AST.ident * Ctypes.type): statement :=
  let (i, t)        := struct_field in
  let (x, call)     := perturb in
  let field_of      := as_field params.(res_params_type) in
  let propose_field := field_of params.(res_params_global_proposal) i t in

  let state_field   := field_of params.(res_params_global_state) i t in
  let proposal      := Ebinop Oadd state_field (Etempvar x t) t in
  Ssequence call (Sassign propose_field proposal).

Definition return_var_pointer (ptr : AST.ident) (ty : Ctypes.type): statement :=
  Sreturn (Some (CStan.Eaddrof (Evar ptr ty) ty)).

Fixpoint over_fieldsM
         (f : AST.ident * Ctypes.type -> mon statement)
         (body: statement)
         (fields: list (AST.ident * Ctypes.type))
  : mon statement :=
  match fields with
  | nil => ret body
  | struct_field::rest =>
    do x <~ f struct_field;
    over_fieldsM f (Ssequence x body) rest
  end.

Definition call_print (p : program) (state_field:expr) (t:Ctypes.type) : mon statement :=
  let errmsg := fun sty => msg ("cannot print type: " ++ sty) in
  match t with
  | Tint _ _ _ => do x <~ Constraints.callmath p MFPrintInt (state_field::nil); ret (snd x)
  | Tlong _ _ => error (errmsg "long")
  | Tfloat _ _ => do x <~ Constraints.callmath p MFPrintDouble (state_field::nil); ret (snd x)

  | Tarray (Tint a b c) len _ => do x <~ Constraints.callmath p MFPrintArrayInt ((Econst_int (Int.repr len) (Tint a b c))::state_field::nil); ret (snd x)
  | Tarray (Tlong _ _) _ _ => error (errmsg "array<long>")
  | Tarray (Tfloat _ _) _ _ => error (errmsg "array<float>")

  | Tpointer _ _ => error (errmsg "pointer")
  | Tfunction _ _ _ => error (errmsg "function")
  | Tstruct _ _ => error (errmsg "struct")
  | Tunion _ _ => error (errmsg "union")
  | Tvoid => error (errmsg "void")
  | _ => error (errmsg "<unknown>")
  end.

Definition print_field (p : program) (v:AST.ident) (gt: AST.ident) (struct_field : AST.ident * Ctypes.type): mon statement :=
  let (i, t) := struct_field in
  call_print p (as_fieldp gt v i t) t.

Definition print_struct (p : program) (v:AST.ident) (gt: AST.ident) (fields: list (AST.ident * Ctypes.type)): mon statement :=
  do pend <~ Constraints.callmath p MFPrintEnd nil;
  do pfields <~ over_fieldsM (print_field p v gt) (snd pend) fields;
  do pstart <~ Constraints.callmath p MFPrintStart nil;
  ret (Ssequence (snd pstart) pfields).

Definition cons_tail {X:Type} (x : X) (xs : list X) :=
  match xs with
  | nil => x::nil
  | h :: rest => h :: x :: rest
  end.

Definition transf_statement_toplevel (p: program) (f: function): mon (list (AST.ident * Ctypes.type) * list (AST.ident * Ctypes.type) * statement * type) :=
  let data := p.(prog_data_struct) in
  let darg := CStan.Evar data.(res_data_arg) (tptr tvoid) in
  let dtmp := data.(res_data_tmp) in

  let params := p.(prog_parameters_struct) in
  let parg := CStan.Evar params.(res_params_arg) (tptr tvoid) in
  let ptmp := params.(res_params_tmp) in

  let TParamStruct := Tstruct params.(res_params_type) noattr in
  let TParamStructp := tptr TParamStruct in

  let TDataStruct := Tstruct data.(res_data_type) noattr in
  let TDataStructp := tptr TDataStruct in

  let data_map := {| is_member := in_list (List.map fst p.(prog_data_vars)); transl := as_field data.(res_data_type) data.(res_data_global); |} in
  let cast := fun arg tmp ty => Sassign (Evar tmp ty) (CStan.Ecast arg ty) in

  match f.(fn_blocktype) with
  | BTModel =>
    let params_map := {|
      is_member := in_list (List.map fst p.(prog_parameters_vars));
      transl := as_fieldp params.(res_params_type) ptmp;
    |} in

    let body := Ssequence (cast parg ptmp TParamStructp) f.(fn_body) in
    do body <~ transf_statement params_map body;
    do body <~ transf_statement data_map body;

    ret (cons_tail (params.(res_params_arg), tptr tvoid) f.(fn_params), (ptmp, TParamStructp)::f.(fn_vars), body, f.(fn_return))

  (* | BTParameters => *)
  (*   do init <~ init_unconstrained p; *)
  (*   let body := over_fields (init_params params init) f.(fn_body) p.(prog_parameters_vars) in *)
  (*   ret (f.(fn_params), (params.(res_params_global_state), TParamStruct)::f.(fn_vars), body, f.(fn_return)) *)

  (* | BTData => *)
  (*   do body <~ transf_statement data_map f.(fn_body); *)
  (*   ret (f.(fn_params), f.(fn_vars), body, f.(fn_return)) *)

  (* | BTGetState => *)
  (*   let body := *)
  (*         Ssequence *)
  (*           f.(fn_body) *)
  (*           (return_var_pointer params.(res_params_global_state) TParamStructp) in *)
  (*   ret (f.(fn_params), f.(fn_vars), body, tptr tvoid) *)

  (* | BTSetState => *)
  (*   let body := *)
  (*       Ssequence *)
  (*         (cast parg ptmp TParamStructp) *)
  (*         (Ssequence *)
  (*           f.(fn_body) *)
  (*           (Sassign (Evar params.(res_params_global_state) TParamStruct) *)
  (*                    (Ederef (Evar ptmp TParamStructp) TParamStruct))) *)
  (*   in *)
  (*   ret ((params.(res_params_arg), tptr tvoid)::f.(fn_params), (ptmp, TParamStructp)::f.(fn_vars), body, f.(fn_return)) *)

  (* | BTSetData => *)
  (*   let body := *)
  (*       Ssequence *)
  (*         (cast darg dtmp TDataStructp) *)
  (*         (Ssequence *)
  (*           f.(fn_body) *)
  (*           (Sassign (Evar data.(res_data_global) TDataStruct) *)
  (*                    (Ederef (Evar dtmp TDataStructp) TDataStruct))) *)
  (*   in *)
  (*   ret ((data.(res_data_arg), tptr tvoid)::f.(fn_params), (dtmp, TDataStructp)::f.(fn_vars), body, f.(fn_return)) *)

  (* | BTPropose => *)
  (*   do init <~ init_unconstrained p; *)
  (*   let body := over_fields (adjust_proposal params init) f.(fn_body) p.(prog_parameters_vars) in *)
  (*   let body := Ssequence body (return_var_pointer params.(res_params_global_proposal) TParamStructp) in *)
  (*   ret (f.(fn_params), f.(fn_vars), body, tptr tvoid) *)

  (* | BTPrintState =>  *)
  (*   do body <~ print_struct p ptmp params.(res_params_type) p.(prog_parameters_vars);  *)
  (*   let body := Ssequence (cast parg ptmp TParamStructp) body in  *)
  (*   ret ((params.(res_params_arg), tptr tvoid)::f.(fn_params), (ptmp, TParamStructp)::f.(fn_vars), body, f.(fn_return))  *)
  (*| BTPrintState => ret (f.(fn_params), f.(fn_vars), f.(fn_body), f.(fn_return)) *)

  (* | BTPrintData => *)
  (*   do body <~ print_struct p dtmp data.(res_data_type) p.(prog_data_vars); *)

  (*   let body := Ssequence (cast darg dtmp TDataStructp) body in *)
  (*   ret ((data.(res_data_arg), tptr tvoid)::f.(fn_params), (dtmp, TDataStructp)::f.(fn_vars), body, f.(fn_return)) *)
  (* | BTPrintData => ret (f.(fn_params), f.(fn_vars), f.(fn_body), f.(fn_return)) *)

  | _ => ret (f.(fn_params), f.(fn_vars), f.(fn_body), f.(fn_return))

  end.

Definition transf_function (p:CStan.program) (f: function): res function :=
  match transf_statement_toplevel p f f.(fn_generator) with
  | SimplExpr.Err msg => Error msg
  | SimplExpr.Res (params, vars, tbody, rtype) g i =>
    OK {|
      fn_body := tbody;
      fn_params := params;
      fn_vars := vars;
      fn_return := rtype;

      (* NOTE only extract gen_trail here *)
      fn_temps := g.(SimplExpr.gen_trail) ++ f.(fn_temps);
      (* fn_temps := g.(SimplExpr.gen_trail); *)
      fn_generator := g;

      fn_callconv := f.(fn_callconv);
      fn_blocktype := f.(fn_blocktype);
    |}
  end.

(* ================================================================== *)
(*                    Switch to Error Monad                           *)
(* ================================================================== *)

Definition transf_external (ef: AST.external_function) : res AST.external_function :=
  match ef with
  | AST.EF_external n sig => OK (AST.EF_external n sig) (*link to blas ops?*)
  | AST.EF_runtime n sig => OK (AST.EF_runtime n sig) (*link runtime?*)
  | _ => OK ef
  end.

Definition transf_fundef (p:CStan.program) (id: AST.ident) (fd: CStan.fundef) : res CStan.fundef :=
  match fd with
  | Internal f => do tf <- transf_function p f; OK (Internal tf)
  | External ef targs tres cc => do ef <- transf_external ef; OK (External ef targs tres cc)
  end.

Definition transf_variable (id: AST.ident) (v: type): res type :=
  OK v.

Definition transf_program(p: CStan.program): res CStan.program :=
  do p1 <- AST.transform_partial_program2 (transf_fundef p) transf_variable p;
  OK {|
      prog_defs := AST.prog_defs p1;
      prog_public := AST.prog_public p1;

      (* FIXME: should we filter the global list to remove these variables? *)
      prog_data_vars:=p.(prog_data_vars);
      prog_data_struct:= p.(prog_data_struct);

      prog_constraints :=p.(prog_constraints);
      (* FIXME: also here: should we filter the global list to remove these variables? *)
      prog_parameters_vars:= p.(prog_parameters_vars);
      prog_parameters_struct:= p.(prog_parameters_struct);

      prog_model:=p.(prog_model);
      prog_target:=p.(prog_target);
      prog_main:=p.(prog_main);

      prog_types:=p.(prog_types);
      prog_comp_env:=p.(prog_comp_env);
      prog_comp_env_eq:=p.(prog_comp_env_eq);

      prog_math_functions:= p.(prog_math_functions);
      prog_dist_functions:= p.(prog_dist_functions);
    |}.
