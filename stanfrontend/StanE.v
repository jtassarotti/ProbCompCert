Require Import Integers.
Require Import Coqlib.
Require Import Floats.
Require Import AST.
Require Ctypes. 

(* For the semantics *)
Require Import Maps.
Require Import Values. 

Inductive b_op :=
  | Plus
  | Minus
  | Times
  | Divide
  | Modulo
  | Or
  | And
  | Equals
  | NEquals
  | Less
  | Leq
  | Greater
  | Geq.

Inductive u_op :=
  | PNot.

Inductive basic :=
  | Bint
  | Breal
  | Barray: basic -> Z -> basic
  | Bfunction: basiclist -> basic -> basic
with basiclist :=
  | Bnil: basiclist
  | Bcons: basic -> basiclist -> basiclist.

Inductive expr :=
  | Econst_int: int -> basic -> expr
  | Econst_float: float -> basic -> expr
  | Evar: ident -> basic -> expr
  | Ecall: expr -> exprlist -> basic -> expr
  | Eunop: u_op -> expr -> basic -> expr
  | Ebinop: expr -> b_op -> expr -> basic -> expr
  | Eindexed: expr -> exprlist -> basic -> expr
  | Etarget: basic -> expr
with exprlist :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.


Inductive constraint :=
  | Cidentity
  | Clower: float -> constraint
  | Cupper: float -> constraint
  | Clower_upper: float -> float -> constraint.

Inductive statement :=
  | Sskip : statement
  | Sassign : expr -> option b_op -> expr -> statement
  | Ssequence: statement -> statement -> statement
  | Sifthenelse: expr -> statement -> statement -> statement
  | Sfor: ident -> expr -> expr -> statement -> statement
  | Starget: expr -> statement
  | Stilde: expr -> expr -> list expr -> statement.

Record variable := mkvariable {
  vd_type: basic;
  vd_constraint: constraint;
}.

Record function := mkfunction {
  fn_return: option(basic);
  fn_params: list (basic * ident);
  fn_body: statement;
  fn_vars: list (ident * basic);
}.

Definition fundef := Ctypes.fundef function.

Record program := mkprogram {
  pr_defs: list (ident * globdef fundef variable);
  pr_parameters_vars: list (ident * basic);
  pr_data_vars: list (ident * basic);
}.

Definition program_of_program (p: program) : AST.program fundef variable :=
  {| AST.prog_defs := p.(pr_defs);
     AST.prog_public := nil;
     AST.prog_main := xH |}.

Coercion program_of_program: program >-> AST.program.

Section EXPR.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)

.

End EXPR.
