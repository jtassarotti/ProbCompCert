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
Require Import SimplExpr. 
Require Import Clightdefs. 
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.


Notation "'do' X <~ A ; B" := (SimplExpr.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

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

Definition cons_tail {X:Type} (x : X) (xs : list X) :=
  match xs with
  | nil => x::nil
  | h :: rest => h :: x :: rest
  end.

Definition transf_statement_toplevel (p: program) (f: function): mon (list (AST.ident * Ctypes.type) * list (AST.ident * Ctypes.type) * statement * type) :=

  let darg := CStan.Evar $"__d__" (tptr tvoid) in
  let dtmp := $"__dt__" in

  let parg := CStan.Evar $"__p__" (tptr tvoid) in
  let ptmp := $"__pt__" in

  let TParamStruct := Tstruct $"Params" noattr in 
  let TParamStructp := tptr TParamStruct in

  let TDataStruct := Tstruct $"Data" noattr in
  let TDataStructp := tptr TDataStruct in

  let data_map := {| is_member := in_list (List.map fst p.(prog_data_vars)); transl := as_field $"Data" $"observations"; |} in
  let cast := fun arg tmp ty => Sassign (Evar tmp ty) (CStan.Ecast arg ty) in

  let params_map := {|
      is_member := in_list (List.map fst p.(prog_parameters_vars));
      transl := as_fieldp $"Params" ptmp; 
    |} in

    let body := Ssequence (cast parg ptmp TParamStructp) f.(fn_body) in
    do body <~ transf_statement params_map body;
    do body <~ transf_statement data_map body;

    ret (cons_tail ($"__p__", tptr tvoid) f.(fn_params), (ptmp, TParamStructp)::f.(fn_vars), body, f.(fn_return))
.

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
      fn_temps := g.(SimplExpr.gen_trail); (* ++ f.(fn_temps);*)
      (* fn_temps := g.(SimplExpr.gen_trail); *)
      fn_generator := g;

      fn_callconv := f.(fn_callconv);
      fn_blocktype := f.(fn_blocktype);
    |}
  end.

Definition transf_program := CStan.transf_program (transf_function).

