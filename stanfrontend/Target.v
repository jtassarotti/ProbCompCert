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
Require AST.
Require SimplExpr.

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
Notation error_mmap := Errors.mmap.

Definition mon_fmap {A B : Type} (f: A -> B) (m: mon A)  : mon B := do a <~ m; ret (f a).

Definition option_fmap {X Y:Type} (f: X -> Y) (o: option X) : option Y :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint mon_mmap {A B : Type} (f: A -> mon B) (l: list A) {struct l} : mon (list B) :=
  match l with
  | nil => ret nil
  | hd :: tl =>
    do hd' <~ f hd;
    do tl' <~ mon_mmap f tl;
    ret (hd' :: tl')
  end.

Fixpoint res_mmap {A B : Type} (f: A -> res B) (l: list A) {struct l} : res (list B) :=
  match l with
  | nil => OK nil
  | hd :: tl =>
    do hd' <- f hd;
    do tl' <- res_mmap f tl;
    OK (hd' :: tl')
  end.

Definition option_mon_mmap {X Y:Type} (f: X -> mon Y) (ox: option X) : mon (option Y) :=
  match ox with
  | None => ret None
  | Some x => do x <~ f x; ret (Some x)
  end.

Definition option_res_mmap {X Y:Type} (f: X -> res Y) (ox: option X) : res (option Y) :=
  match ox with
  | None => OK None
  | Some x => do x <- f x; OK (Some x)
  end.

Definition maybe_ident (e: expr): option AST.ident :=
match e with
  | CStan.Evar i t => Some i
  | CStan.Etempvar i t => Some i
  | _ => None
end.

Fixpoint transf_starget_statement (s: CStan.statement) {struct s}: res CStan.statement :=
  match s with
  | Sskip => OK Sskip
  | Sbreak => OK Sbreak
  | Scontinue => OK Scontinue
  | Sassign e0 e1 => OK (Sassign e0 e1)
  | Sset i e => OK (Sset i e)
  | Scall oi e le => OK (Scall oi e le)
  | Sreturn oe => OK (Sreturn oe)
  | Sbuiltin oi ef lt le => Error (msg "OK (Sbuiltin oi ef lt le)")

  | Ssequence s0 s1 =>
    do s0 <- transf_starget_statement s0;
    do s1 <- transf_starget_statement s1;
    OK (Ssequence s0 s1)

  | Sifthenelse e s0 s1 =>
    do s0 <- transf_starget_statement s0;
    do s1 <- transf_starget_statement s1;
    OK (Sifthenelse e s0 s1)

  | Sloop s0 s1 =>
    do s0 <- transf_starget_statement s0;
    do s1 <- transf_starget_statement s1;
    OK (Sloop s0 s1)

  | Starget e =>
    OK (Sassign (Etarget tdouble)
              (Ebinop Cop.Oadd
                      (Etarget tdouble) e tdouble))

  | Stilde e i le (oe0, oe1) => Error (msg "Stilde DNE in this stage of pipeline")
end.

Fixpoint transf_etarget_expr (ot : AST.ident) (e: CStan.expr) {struct e}: res CStan.expr :=
  match e with
  | CStan.Econst_int i t => OK (CStan.Econst_int i t)
  | CStan.Econst_float f t => OK (CStan.Econst_float f t)
  | CStan.Econst_single f t => OK (CStan.Econst_single f t)
  | CStan.Econst_long i t => OK (CStan.Econst_long i t)
  | CStan.Evar i t => OK (CStan.Evar i t)
  | CStan.Etempvar i t => OK (CStan.Etempvar i t)
  | CStan.Ederef e t =>
    do e <- transf_etarget_expr ot e;
    OK (CStan.Ederef e t)
  | CStan.Ecast e t => OK (CStan.Ecast e t)
  | CStan.Efield e i t => OK (CStan.Efield e i t)
  | CStan.Eunop uop e t =>
    do e <- transf_etarget_expr ot e;
    OK (CStan.Eunop uop e t)
  | CStan.Ebinop bop e0 e1 t =>
    do e0 <- transf_etarget_expr ot e0;
    do e1 <- transf_etarget_expr ot e1;
    OK (CStan.Ebinop bop e0 e1 t)
  | CStan.Eaddrof e t => OK (CStan.Eaddrof e t)
  | CStan.Esizeof t0 t1 => OK (CStan.Esizeof t0 t1)
  | CStan.Ealignof t0 t1 => OK (CStan.Ealignof t0 t1)
  | CStan.Etarget ty => OK (CStan.Evar ot ty)
end.

Fixpoint transf_etarget_statement (t : AST.ident) (s: CStan.statement) {struct s}: res CStan.statement :=
match s with
  | Sassign e0 e1 =>
    do e0 <- transf_etarget_expr t e0;
    do e1 <- transf_etarget_expr t e1;
    OK (Sassign e0 e1)
  | Sset i e =>
    do e <- transf_etarget_expr t e;
    if Pos.eqb i t
    then Error (msg "cannot set the target identifier")
    else OK (Sset i e)
  | Scall oi e le =>
    do e <- transf_etarget_expr t e;
    do le <- res_mmap (transf_etarget_expr t) le;
    OK (Scall oi e le)
  | Sbuiltin oi ef lt le =>
    do le <- res_mmap (transf_etarget_expr t) le;
    OK (Sbuiltin oi ef lt le)
  | Ssequence s0 s1 =>
    do s0 <- transf_etarget_statement t s0;
    do s1 <- transf_etarget_statement t s1;
    OK (Ssequence s0 s1)
  | Sifthenelse e s0 s1 =>
    do e <- transf_etarget_expr t e;
    do s0 <- transf_etarget_statement t s0;
    do s1 <- transf_etarget_statement t s1;
    OK (Sifthenelse e s0 s1)
  | Sloop s0 s1 =>
    do s0 <- transf_etarget_statement t s0;
    do s1 <- transf_etarget_statement t s1;
    OK (Sloop s0 s1)
  | Sreturn oe =>
    do oe <- option_res_mmap (transf_etarget_expr t) oe;
    OK (Sreturn oe)
  | Starget e =>
    Error (msg "Starget DNE in this stage of pipeline")
  | Stilde e i le (oe0, oe1) =>
    Error (msg "Stilde DNE in this stage of pipeline")
  | Sbreak => OK Sbreak
  | Sskip => OK Sskip
  | Scontinue => OK Scontinue
end.

Definition transf_statement (t: AST.ident) (body: statement) : res CStan.statement :=
  do body <- transf_starget_statement body;
  transf_etarget_statement t body.

Definition add_prelude_epilogue (body: statement) : CStan.statement :=
  let tytarget := tdouble in
  let prelude  := Starget (Econst_float Float.zero tytarget) in
  let epilogue := Sreturn (Some (CStan.Etarget tytarget)) in
  Ssequence prelude (Ssequence body epilogue).

Definition transf_model_body (f: function): statement :=
match f.(fn_blocktype) with
| BTModel => add_prelude_epilogue f.(fn_body)
| _ => f.(fn_body)
end.

Definition transf_function (tgt: AST.ident) (f: function): res function :=
  do body <- transf_statement tgt (transf_model_body f);
  OK {|
      fn_params := f.(fn_params);
      fn_body := body;

      fn_temps := f.(fn_temps);
      fn_vars := f.(fn_vars);
      fn_generator := f.(fn_generator);

      (*should not change*)
      fn_return := f.(fn_return);
      fn_callconv := f.(fn_callconv);
      fn_blocktype := f.(fn_blocktype);
     |}.

Definition transf_external (ef: AST.external_function) : res AST.external_function :=
  match ef with
  | AST.EF_external n sig => OK (AST.EF_external n sig) (*link to blas ops?*)
  | AST.EF_runtime n sig => OK (AST.EF_runtime n sig) (*link runtime?*)
  | _ => OK ef
  end.

Definition transf_fundef (tgt: AST.ident) (fd: CStan.fundef) : res CStan.fundef :=
  match fd with
  | Internal f => do tf <- transf_function tgt f; OK (Internal tf)
  | External ef targs tres cc => do ef <- transf_external ef; OK (External ef targs tres cc)
  end.

Definition transf_variable (v: type): res type :=
  OK v.

Definition transf_program (p: CStan.program): res CStan.program :=
  do p1 <- AST.transform_partial_program2 (fun i => transf_fundef p.(prog_target)) (fun i => transf_variable) p;
  OK {|
      prog_defs := AST.prog_defs p1;
      prog_public := AST.prog_public p1;

      prog_data:=p.(prog_data);
      prog_data_vars:=p.(prog_data_vars);
      prog_data_struct:= p.(prog_data_struct);
      prog_transformed_data:=p.(prog_transformed_data);

      prog_constraints := p.(prog_constraints);
      prog_parameters:= p.(prog_parameters);
      prog_parameters_vars:= p.(prog_parameters_vars);
      prog_parameters_struct:= p.(prog_parameters_struct);
      prog_transformed_parameters:=p.(prog_transformed_parameters);

      prog_generated_quantities:=p.(prog_generated_quantities);
      prog_model:=p.(prog_model);
      prog_target:=p.(prog_target);
      prog_main:=p.(prog_main);

      prog_types:=p.(prog_types);
      prog_comp_env:=p.(prog_comp_env);
      prog_comp_env_eq:=p.(prog_comp_env_eq);

      prog_math_functions:= p.(prog_math_functions);
      prog_dist_functions:= p.(prog_dist_functions);
    |}.
