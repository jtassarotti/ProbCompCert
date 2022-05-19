Require Import CStan. 
Require Import String List ZArith.
Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import Errors.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.


Fixpoint transf_expression (e: CStan.expr) {struct e}: res Clight.expr :=
  match e with
  | CStan.Econst_int i t => OK (Econst_int i t)
  | CStan.Econst_float f t => OK (Econst_float f t)
  | CStan.Econst_single f t => OK (Econst_single f t)
  | CStan.Econst_long i t => OK (Econst_long i t)
  | CStan.Evar i t => OK (Evar i t)
  | CStan.Etempvar i t => OK (Etempvar i t)
  | CStan.Ederef e t => do e <- (transf_expression e); OK (Ederef e t)
  | CStan.Ecast e t => do e <- (transf_expression e); OK (Ecast e t)
  | CStan.Efield e i t => do e <- (transf_expression e); OK (Efield e i t)
  | CStan.Eaddrof e t => do e <- (transf_expression e); OK (Eaddrof e t)
  | CStan.Eunop u e t => 
    do e <- (transf_expression e); 
    OK (Eunop u e t)

  | CStan.Ebinop b e1 e2 t =>
    do e1 <- (transf_expression e1);
    do e2 <- (transf_expression e2); 
    OK (Ebinop b e1 e2 t)
  | CStan.Esizeof t1 t2 => OK (Esizeof t1 t2)
  | CStan.Ealignof t1 t2 => OK (Ealignof t1 t2)
  | CStan.Etarget t => Error (msg "Backend expression: target")
  end.

Fixpoint transf_expression_list (l: list (CStan.expr)) {struct l}: res (list Clight.expr) :=
  match l with
  | nil => OK (nil)
  | cons e l =>
    do e <- (transf_expression e);
    do l <- (transf_expression_list l);
    OK (cons e l)
  end.
	
Fixpoint transf_statement (s: CStan.statement) {struct s}: res Clight.statement :=
  match s with
  | CStan.Sskip => OK Sskip
  | CStan.Sassign e1 e2 =>
    do e1 <- (transf_expression e1);
    do e2 <- (transf_expression e2); 
    OK (Sassign e1 e2)
  | CStan.Sset i e =>
    do e <- (transf_expression e);
    OK (Sset i e)
  | CStan.Scall oi e le =>
    do e <- (transf_expression e);
    do le <- (transf_expression_list le);
    OK (Scall oi e le)
  | CStan.Sbuiltin oi ef t le =>
    do le <- (transf_expression_list le);
    OK (Sbuiltin oi ef t le)			       
  | CStan.Ssequence s1 s2 =>
    do s1 <- (transf_statement s1); 
    do s2 <- (transf_statement s2);
    OK (Ssequence s1 s2)			 
  | CStan.Sifthenelse e s1 s2 =>
    do e <- (transf_expression e); 
    do s1 <- (transf_statement s1); 
    do s2 <- (transf_statement s2);
    OK (Sifthenelse e s1 s2)			 
  | CStan.Sloop s1 s2 =>
    do s1 <- (transf_statement s1); 
    do s2 <- (transf_statement s2);
    OK (Sloop s1 s2)
  | CStan.Sbreak => OK Sbreak
  | CStan.Scontinue => OK Scontinue
  | CStan.Sreturn None => OK (Sreturn None)
  | CStan.Sreturn (Some e) => do e <- (transf_expression e); OK (Sreturn (Some e))
  | CStan.Starget e => Error (msg "Backend: target")
  | CStan.Stilde o e le tr => Error (msg "Backend: tilde")
  end.

Definition transf_variable (v: type): res Ctypes.type :=
  OK v.

Definition transf_function (f: CStan.function): res Clight.function :=
  do body <- transf_statement f.(CStan.fn_body);
  OK {|
      Clight.fn_return := f.(CStan.fn_return);
      Clight.fn_params := f.(CStan.fn_params);
      Clight.fn_body := body; 
      Clight.fn_callconv := f.(CStan.fn_callconv);
      Clight.fn_temps := f.(CStan.fn_temps);
      Clight.fn_vars := f.(CStan.fn_vars);
     |}.

Definition transf_fundef (fd: CStan.fundef) : res Clight.fundef :=
  match fd with
  | Internal f =>
      do tf <- transf_function f; OK (Internal tf)
  | External ef targs tres cc =>
      OK (External ef targs tres cc)
  end.

Definition backend (p: CStan.program): res Clight.program :=
  do p1 <- AST.transform_partial_program2 (fun i => transf_fundef) (fun i => transf_variable) p;
  OK {| 
      Ctypes.prog_defs := AST.prog_defs p1;
      Ctypes.prog_public:= $"model" :: nil;
      Ctypes.prog_main:= $"main"; 
      Ctypes.prog_types:=p.(CStan.prog_types);
      Ctypes.prog_comp_env:=p.(CStan.prog_comp_env);
      Ctypes.prog_comp_env_eq:= p.(CStan.prog_comp_env_eq);
    |}.
