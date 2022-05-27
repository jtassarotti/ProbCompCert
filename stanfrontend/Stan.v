Require Import Globalenvs.
Require Import Events.
Require Import Integers.

Require Import String.
Open Scope string_scope. 

(* OCaml string *)  
Parameter string : Type.

Parameter loc: Type.

Definition identifier := string.

Inductive type :=
  | Tint
  | Treal
  | Tvector
  | Trow
  | Tmatrix
  | Tarray: type -> type.

Inductive autodifftype :=
  | Adata_only 
  | Aauto_diffable.

Inductive operator :=
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
  | Geq
  | PNot

  | PPlus
  | PMinus
  | IntDivide
  | LDivide
  | EltTimes
  | EltDivide
  | Pow
  | EltPow
  | Transpose.

Inductive expr :=
  (* Classical expressions that exist in C *)
  | Econst_int: string -> expr
  | Econst_float: string -> expr
  | Evar: identifier -> expr
  | Eunop: operator -> expr -> expr
  | Ebinop: expr -> operator -> expr -> expr
  | Ecall: identifier -> list expr -> expr
  | Econdition: expr -> expr -> expr -> expr
  (* Classical expresions that differ from C *)
  | Earray: list expr -> expr
  | Erow: list expr -> expr
  | Eindexed: expr -> list index -> expr
  (* Probabilistic expressions *)
  | Edist: identifier -> list expr -> expr
  | Etarget

with index :=
  | Iall
  | Isingle: expr -> index
  | Iupfrom: expr -> index
  | Idownfrom: expr -> index
  | Ibetween: expr -> expr -> index. 
	
Inductive basic :=
  | Bint
  | Breal
  | Bvector: expr -> basic
  | Brow: expr -> basic
  | Bmatrix: expr -> expr -> basic.

Inductive constraint :=
  | Cidentity
  | Clower: expr -> constraint
  | Cupper: expr -> constraint
  | Clower_upper: expr -> expr -> constraint
  | Coffset: expr -> constraint
  | Cmultiplier: expr -> constraint
  | Coffset_multiplier: expr -> expr -> constraint
  | Cordered
  | Cpositive_ordered
  | Csimplex
  | Cunit_vector
  | Ccholesky_corr
  | Ccholesky_cov
  | Ccorrelation
  | Ccovariance.

Record variable := mkvariable {
  vd_id: identifier;
  vd_type: basic;
  vd_constraint: constraint;
  vd_dims: list(expr);
  vd_init: option expr;
  vd_global: bool
}.

Inductive printable := 
  | Pstring: string -> printable 
  | Pexpr: expr -> printable.
  
Inductive statement :=
  (* Classical statements that exist in C *)
  | Sskip : statement
  | Sassign : expr -> option operator -> expr -> statement
  | Sblock: list statement -> statement
  | Sifthenelse: expr -> statement -> statement -> statement
  | Swhile: expr -> statement -> statement
  | Sfor: identifier -> expr -> expr -> statement -> statement
  | Sbreak: statement
  | Scontinue: statement
  | Sreturn: option expr -> statement
  | Svar: variable -> statement
  | Scall: identifier -> list expr -> statement
  | Sprint: list printable -> statement
  | Sreject: list printable -> statement
  (* Classical statements that differ C *)
  | Sforeach: identifier -> expr -> statement -> statement
  (* Probabilistic statements *)
  | Starget: expr -> statement
  | Stilde: expr -> identifier -> list expr -> (option expr * option expr) -> statement.
		      
Record function := mkfunction { 
  fn_return: option(type); 
  fn_name: identifier; 
  fn_params: list (autodifftype * type * identifier);
  fn_body: statement 
}.

Record program := mkprogram {
  pr_functions: option (list function);
  pr_data: option (list variable);
  pr_transformed_data: option (list statement);
  pr_parameters: option (list variable);
  pr_transformed_parameters: option (list statement);
  pr_model: option (list statement);
  pr_generated: option (list statement)
}.
