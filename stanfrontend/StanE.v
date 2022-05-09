Require Import Globalenvs.
Require Import Events.
Require Import Integers.
Require Import Coqlib.
Require Import Floats.
Require Import AST.
Require Stan.
Require CStan.
Require Import Sops.
Require Import Cop.
Require Import Stypes.

Inductive basic :=
  | Bint
  | Breal
  | Barray: Z -> basic
  | Bfunction: basiclist -> option basic -> basic
with basiclist : Type :=
  | Bnil: basiclist
  | Bcons: basic -> basiclist -> basiclist.

Inductive expr :=
  (* Classical expressions that exist in C *)
  (* NOTE basic is a StanE type, see variable.vd_type *)
  | Econst_int: int -> basic -> expr
  | Econst_float: float -> basic -> expr
  | Evar: ident -> basic -> expr
  (* FIXME: add types to all proceeding as well? *)
  | Eunop: operator -> expr -> expr
  | Ebinop: expr -> operator -> expr -> expr
  | Ecall: ident -> list expr -> expr
  | Econdition: expr -> expr -> expr -> expr
  (* Classical expresions that differ from C *)
  | Earray: list expr -> expr
  | Eindexed: expr -> list index -> expr
  (* Probabilistic expressions *)
  | Edist: ident -> list expr -> expr
  | Etarget

with index :=
  | Iall
  | Isingle: expr -> index
  | Iupfrom: expr -> index
  | Idownfrom: expr -> index
  | Ibetween: expr -> expr -> index.

Inductive constraint :=
  | Cidentity
  | Clower: expr -> constraint
  | Cupper: expr -> constraint
  | Clower_upper: expr -> expr -> constraint.

Inductive statement :=
  (* Classical statements that exist in C *)
  | Sskip : statement
  | Sassign : expr -> option operator -> expr -> statement
  | Ssequence: statement -> statement -> statement
  | Sifthenelse: expr -> statement -> statement -> statement
  | Swhile: expr -> statement -> statement
  | Sfor: ident -> expr -> expr -> statement -> statement
  | Sbreak: statement
  | Scontinue: statement
  | Sreturn: option expr -> statement
  | Svar: ident -> basic -> option expr -> statement
  | Scall: ident -> list expr -> statement
  (* Classical statements that differ C *)
  | Sforeach: ident -> expr -> statement -> statement
  (* Probabilistic statements *)
  | Starget: expr -> statement
  | Stilde: expr -> expr -> list expr -> (option expr * option expr) -> statement.

Record variable := mkvariable {
  vd_type: basic;
  vd_constraint: constraint;
}.

Record function := mkfunction {
  fn_return: option(basic);
  fn_params: list (autodifftype * basic * ident);
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
  pr_parameters_struct: CStan.reserved_params;
  pr_data_vars: list (ident * basic);
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
