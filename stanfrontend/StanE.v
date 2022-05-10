Require Import Integers.
Require Import Coqlib.
Require Import Floats.
Require Import AST.
Require CStan.

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
  | Bfunction: basiclist -> option basic -> basic
with basiclist : Type :=
  | Bnil: basiclist
  | Bcons: basic -> basiclist -> basiclist.

Inductive expr :=
  (* Classical expressions that exist in C *)
  | Econst_int: int -> basic -> expr
  | Econst_float: float -> basic -> expr
  | Evar: ident -> basic -> expr
  (* FIXME: add types to all proceeding as well? *)
  | Eunop: u_op -> expr -> expr
  | Ebinop: expr -> b_op -> expr -> expr
  | Ecall: ident -> list expr -> expr
  | Eindexed: expr -> list expr -> expr
  (* Probabilistic expressions *)
  | Edist: ident -> list expr -> expr
  | Etarget.

Inductive constraint :=
  | Cidentity
  | Clower: expr -> constraint
  | Cupper: expr -> constraint
  | Clower_upper: expr -> expr -> constraint.

Inductive statement :=
  (* Classical statements that exist in C *)
  | Sskip : statement
  | Sassign : expr -> option b_op -> expr -> statement
  | Ssequence: statement -> statement -> statement
  | Sifthenelse: expr -> statement -> statement -> statement
  | Sfor: ident -> expr -> expr -> statement -> statement
  (* Probabilistic statements *)
  | Starget: expr -> statement
  | Stilde: expr -> expr -> list expr -> (option expr * option expr) -> statement.

Record variable := mkvariable {
  vd_type: basic;
  vd_constraint: constraint;
}.

Record function := mkfunction {
  fn_return: option(basic);
  fn_params: list (basic * ident);
  fn_body: statement;
  fn_blocktype: CStan.blocktype;
  fn_temps: list (ident * basic);
  fn_vars: list (ident * basic);
}.

Definition fundef := Ctypes.fundef function.

Record program := mkprogram {
  pr_defs: list (ident * globdef fundef variable);
  pr_public: list ident;
  pr_model: ident;
  pr_target: ident;
  pr_parameters_vars: list (ident * basic);
  pr_data_vars: list (ident * basic);
  (* What follows is information for the compiler specifically *)
  pr_parameters_struct: CStan.reserved_params;
  pr_data_struct: CStan.reserved_data;
  pr_main: ident;
  pr_math_functions: list (CStan.math_func * ident * Ctypes.type);
  pr_dist_functions: list (CStan.dist_func * ident);
}.

Definition program_of_program (p: program) : AST.program fundef variable :=
  {| AST.prog_defs := p.(pr_defs);
     AST.prog_public := p.(pr_public);
     AST.prog_main := xH |}.

Coercion program_of_program: program >-> AST.program.
