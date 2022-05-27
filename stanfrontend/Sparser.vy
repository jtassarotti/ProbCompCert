(** The parser for Stan.
    A CoqMenhir file. *)

%{

Require Import String.
Open Scope string_scope.

Require Import List.
Import ListNotations.
Require Import Nat.

Require Import Stan.

(* Takes a sized_basic_type and a list of sizes and repeatedly applies then
   Sarray constructor, taking sizes off the list *)
Definition reducearray (sbt:basic) (l:list expr) : list expr := l.
  (* List.fold_right (fun z y => Sarray y z) sbt l. *)

Fixpoint reparray (n:nat) (x:type) : type :=
  match n with
  | O => x
  | S n' => reparray n' (Tarray x)
  end.

Definition omap {A:Type} {B:Type} (f:A->B) (x:option A): option B :=
  match x with
  | None => None
  | Some a => Some (f a)
  end.

Definition sizes d : list expr :=
  match d with
  | None => []
  | Some l => l
  end.

%}
  

%token <loc> FUNCTIONBLOCK DATABLOCK TRANSFORMEDDATABLOCK PARAMETERSBLOCK
       TRANSFORMEDPARAMETERSBLOCK MODELBLOCK GENERATEDQUANTITIESBLOCK
%token <loc> LBRACE RBRACE LPAREN RPAREN LBRACK RBRACK LABRACK RABRACK COMMA SEMICOLON
       BAR
%token <loc> RETURN IF_ ELSE WHILE FOR IN BREAK CONTINUE
%token <loc> VOID INT REAL VECTOR ROWVECTOR MATRIX ORDERED POSITIVEORDERED SIMPLEX
       UNITVECTOR CHOLESKYFACTORCORR CHOLESKYFACTORCOV CORRMATRIX COVMATRIX
%token <loc> LOWER UPPER OFFSET MULTIPLIER
%token <string * loc> INTNUMERAL
%token <string * loc> REALNUMERAL
%token <string * loc> STRINGLITERAL
%token <string * loc> IDENTIFIER
%token <loc> TARGET
%token <loc> QMARK COLON BANG MINUS PLUS HAT ELTPOW TRANSPOSE TIMES DIVIDE MODULO IDIVIDE
       LDIVIDE ELTTIMES ELTDIVIDE OR AND EQUALS NEQUALS LEQ GEQ TILDE
%token <loc> ASSIGN PLUSASSIGN MINUSASSIGN TIMESASSIGN DIVIDEASSIGN
   ELTDIVIDEASSIGN ELTTIMESASSIGN
%token <loc> PRINT REJECT
%token <loc> TRUNCATE
%token <loc> EOF

(* type declarations for nonterminals *)

%type <expr> lhs expr or_expr and_expr equal_expr comparison_expr additive_expr multiplicative_expr leftdivide_expr prefix_expr exponentiation_expr postfix_expr common_expr basic_expr constr_expr index_expr
%type <list expr> dims
%type <list index> index indexes
%type <list printable> printable printables
%type <string> string_literal, identifier, decl_identifier
%type <option operator> assignment_op
%type <statement> statement atomic_statement open_statement closed_statement simple_statement top_vardecl_or_statement vardecl_or_statement var_decl top_var_decl
%type <variable> top_var_decl_no_assign
%type <list statement> transformed_data_block transformed_parameters_block model_block generated_quantities_block
%type <list variable> data_block parameters_block
%type <list function> function_block
%type <option expr * option expr> truncation
%type <constraint> range offset_mult range_constraint type_constraint
%type <basic * constraint> top_var_type
%type <basic> sized_basic_type
%type <type> basic_type unsized_type
%type <nat> unsized_dims (* questionable *)
%type <autodifftype * type * string> arg_decl
%type <option(type)> return_type
%type <function> function_def

%type <option (list variable)> option(data_block) option(parameters_block) 
%type <option (list function)> option(function_block)
%type <option (list statement)> option(transformed_data_block) option(transformed_parameters_block) option(model_block) option(generated_quantities_block)

%type <list expr> separated_nonempty_list(COMMA,expr) separated_list(COMMA,expr)
%type <list (autodifftype * type * string) > separated_nonempty_list(COMMA,arg_decl) separated_list(COMMA,arg_decl)
%type <loc * expr> pair(COMMA,expr)  pair(ASSIGN,expr)
%type <option expr> option(expr)
%type <option (list expr)> option(dims)
%type <option (loc * expr)> option(pair(COMMA,expr)) option(pair(ASSIGN,expr))
%type <option (option expr * option expr)> option(truncation)
%type <list statement> list(vardecl_or_statement) list(top_vardecl_or_statement) 
%type <list variable> list(top_var_decl_no_assign)
%type <list function> list(function_def)
%type <list loc> list(COMMA)
(* Grammar *)

(* Top level rule *)

%start <program> program
%%

(* copied from stdlib *)
option(X):
  | { None }
  | x = X { Some x }

list(X):
  | { [] }
  | x = X; xs = list(X) { x :: xs }

separated_list(separator, X):
 | {[]}
 | xs =separated_nonempty_list(separator, X) { xs }

separated_nonempty_list(separator, X):
  | x = X { [ x ] }
  | x = X; separator; xs = separated_nonempty_list(separator, X) { x :: xs }

 pair(X, Y):
  | x = X; y = Y { pair x y }

(* program *)
program:
  | ofb=option(function_block)
    odb=option(data_block)
    otdb=option(transformed_data_block)
    opb=option(parameters_block)
    otpb=option(transformed_parameters_block)
    omb=option(model_block)
    ogb=option(generated_quantities_block)
    EOF { mkprogram ofb odb otdb opb otpb omb ogb }

function_block:
  | FUNCTIONBLOCK LBRACE fd=list(function_def) RBRACE {fd}

data_block:
  | DATABLOCK LBRACE tvd=list(top_var_decl_no_assign) RBRACE { tvd }

transformed_data_block:
  | TRANSFORMEDDATABLOCK LBRACE tvds=list(top_vardecl_or_statement) RBRACE { tvds }

parameters_block:
  | PARAMETERSBLOCK LBRACE tvd=list(top_var_decl_no_assign) RBRACE { tvd }

transformed_parameters_block:
  | TRANSFORMEDPARAMETERSBLOCK LBRACE tvds=list(top_vardecl_or_statement) RBRACE { tvds }

model_block:
  | MODELBLOCK LBRACE vds=list(vardecl_or_statement) RBRACE { vds  }

generated_quantities_block:
  | GENERATEDQUANTITIESBLOCK LBRACE tvds=list(top_vardecl_or_statement) RBRACE { tvds }

identifier:
  | id=IDENTIFIER { fst id }

decl_identifier:
  | id=identifier { id }

function_def:
  | rt=return_type name=decl_identifier LPAREN args=separated_list(COMMA, arg_decl) RPAREN b=statement
    { mkfunction rt name args b }

return_type:
  | VOID { None }
  | ut=unsized_type { Some ut }

arg_decl:
  | ut=unsized_type id=decl_identifier { (Aauto_diffable, ut, id) }
  | DATABLOCK ut=unsized_type id=decl_identifier { (Adata_only, ut, id) }

unsized_type:
  | bt=basic_type { reparray 0 bt    }
  | bt=basic_type d=unsized_dims { reparray (1+d) bt    }

basic_type:
  | INT { Tint }
  | REAL { Treal }
  | VECTOR { Tvector }
  | ROWVECTOR { Trow }
  | MATRIX { Tmatrix }

unsized_dims:
  | LBRACK cs=list(COMMA) RBRACK { length cs }

(* declarations *)
var_decl:
  | sbt=sized_basic_type id=decl_identifier d=option(dims) ae=option(pair(ASSIGN, expr)) SEMICOLON
    { Svar (mkvariable id sbt Cidentity (sizes d) (omap snd ae) false) }

sized_basic_type:
  | INT { Bint }
  | REAL { Breal }
  | VECTOR LBRACK e=expr RBRACK { Bvector e }
  | ROWVECTOR LBRACK e=expr RBRACK { Brow e  }
  | MATRIX LBRACK e1=expr COMMA e2=expr RBRACK { Bmatrix e1 e2 }

top_var_decl_no_assign:
  | tvt=top_var_type id=decl_identifier d=option(dims) SEMICOLON
    { mkvariable id (fst tvt) (snd tvt) ((reducearray (fst tvt) (sizes d))) None true }

top_var_decl:
  | tvt=top_var_type id=decl_identifier d=option(dims) ass=option(pair(ASSIGN, expr)) SEMICOLON
    { Svar (mkvariable id (fst tvt) (snd tvt) ((reducearray (fst tvt) (sizes d))) (omap snd ass) true) }

top_var_type:
  | INT r=range_constraint { (Bint, r) }
  | REAL c=type_constraint { (Breal, c) }
  | VECTOR c=type_constraint LBRACK e=expr RBRACK { (Bvector e, c) }
  | ROWVECTOR c=type_constraint LBRACK e=expr RBRACK { (Brow e, c) }
  | MATRIX c=type_constraint LBRACK e1=expr COMMA e2=expr RBRACK { (Bmatrix e1 e2, c) }
  | ORDERED LBRACK e=expr RBRACK { (Bvector e, Cordered) }
  | POSITIVEORDERED LBRACK e=expr RBRACK { (Bvector e, Cpositive_ordered) }
  | SIMPLEX LBRACK e=expr RBRACK { (Bvector e, Csimplex) }
  | UNITVECTOR LBRACK e=expr RBRACK { (Bvector e, Cunit_vector) }
  | CHOLESKYFACTORCORR LBRACK e=expr RBRACK { (Bmatrix e e, Ccholesky_corr) }
  | CHOLESKYFACTORCOV LBRACK e1=expr oe2=option(pair(COMMA, expr)) RBRACK
    { 
      match oe2 with 
      | Some (_,e2) => ( Bmatrix e1 e2, Ccholesky_cov)
      | _           =>  (Bmatrix e1 e1, Ccholesky_cov)
      end
    }
  | CORRMATRIX LBRACK e=expr RBRACK { (Bmatrix e e, Ccorrelation) }
  | COVMATRIX LBRACK e=expr RBRACK { (Bmatrix e e, Ccovariance) }

type_constraint:
  | r=range_constraint { r }
  | LABRACK l=offset_mult RABRACK { l }

range_constraint:
  | { Cidentity }
  | LABRACK r=range RABRACK { r }

range:
  | LOWER ASSIGN e1=constr_expr COMMA UPPER ASSIGN e2=constr_expr
  | UPPER ASSIGN e2=constr_expr COMMA LOWER ASSIGN e1=constr_expr { Clower_upper e1 e2 }
  | LOWER ASSIGN e=constr_expr { Clower e }
  | UPPER ASSIGN e=constr_expr { Cupper e }

offset_mult:
  | OFFSET ASSIGN e1=constr_expr COMMA MULTIPLIER ASSIGN e2=constr_expr
  | MULTIPLIER ASSIGN e2=constr_expr COMMA OFFSET ASSIGN e1=constr_expr { Coffset_multiplier e1 e2 }
  | OFFSET ASSIGN e=constr_expr { Coffset e }
  | MULTIPLIER ASSIGN e=constr_expr { Cmultiplier e }

dims:
  | LBRACK l=separated_nonempty_list(COMMA, expr) RBRACK { l }

(* exprs *)
expr:
  | e1=or_expr  QMARK e2=expr COLON e3=expr { Econdition e1 e2 e3 }
  | e=or_expr { e }

or_expr:
  | e1 = or_expr OR e2=and_expr { Ebinop e1 Or e2 }
  | e = and_expr { e }

and_expr:
  | e1=and_expr AND e2=equal_expr { Ebinop e1 And e2 }
  | e=equal_expr { e }

equal_expr:
  | e1=equal_expr EQUALS e2=comparison_expr { Ebinop e1 Equals e2 }
  | e1=equal_expr NEQUALS e2=comparison_expr { Ebinop e1 NEquals e2 }
  | e = comparison_expr { e }

comparison_expr:
  | e1=comparison_expr LABRACK e2=additive_expr { Ebinop e1 Less e2 }
  | e1=comparison_expr LEQ e2=additive_expr { Ebinop e1 Leq e2 }  
  | e1=comparison_expr RABRACK e2=additive_expr { Ebinop e1 Greater e2 }    
  | e1=comparison_expr GEQ e2=additive_expr { Ebinop e1 Geq e2 }
  | e=additive_expr { e }

additive_expr:
  | e1=additive_expr PLUS e2=multiplicative_expr { Ebinop e1 Plus e2 }
  | e1=additive_expr MINUS e2=multiplicative_expr { Ebinop e1 Minus e2 }
  | e=multiplicative_expr { e }

multiplicative_expr:
  | e1=multiplicative_expr TIMES e2=leftdivide_expr { Ebinop e1 Times e2 }
  | e1=multiplicative_expr DIVIDE e2=leftdivide_expr { Ebinop e1 Divide e2 }  
  | e1=multiplicative_expr IDIVIDE e2=leftdivide_expr { Ebinop e1 IntDivide e2 }
  | e1=multiplicative_expr MODULO e2=leftdivide_expr { Ebinop e1 Modulo e2 }  
  | e1=multiplicative_expr ELTTIMES e2=leftdivide_expr { Ebinop e1 EltTimes e2 }
  | e1=multiplicative_expr ELTDIVIDE e2=leftdivide_expr { Ebinop e1 EltDivide e2 }
  | e=leftdivide_expr { e }

leftdivide_expr:
  | e1=leftdivide_expr LDIVIDE e2=prefix_expr { Ebinop e1 LDivide e2 }
  | e=prefix_expr { e }

prefix_expr:
  | BANG e=exponentiation_expr { Eunop PNot e }
  | MINUS e=exponentiation_expr { Eunop PMinus e }
  | PLUS e=exponentiation_expr { Eunop PPlus e }
  | e=exponentiation_expr { e }

exponentiation_expr:
  | e1=postfix_expr HAT e2=exponentiation_expr { Ebinop e1 Pow e2 }
  | e1=postfix_expr ELTPOW e2=exponentiation_expr { Ebinop e1 EltPow e2 }
  | e=postfix_expr { e }

postfix_expr: 
  | e=postfix_expr TRANSPOSE { Eunop Transpose e }
  | e = index_expr { e }
  | e=common_expr { e }

index_expr:
  | e=basic_expr LBRACK indices=indexes RBRACK { Eindexed e indices }

common_expr:
  | e=basic_expr { e}
  | l=lhs { l}

basic_expr:
  | i=INTNUMERAL { Econst_int (fst i) }
  | r=REALNUMERAL { Econst_float (fst r) }
  | LBRACE xs=separated_nonempty_list(COMMA, expr) RBRACE { Earray xs }
  | LBRACK xs=separated_list(COMMA, expr) RBRACK { Erow xs }
  | id=identifier LPAREN e=expr BAR args=separated_list(COMMA, expr) RPAREN { Edist id (e :: args) }
  | id=identifier LPAREN args=separated_list(COMMA, expr) RPAREN { Ecall id args }
  | TARGET LPAREN RPAREN { Etarget }
  | LPAREN e=expr RPAREN { e }

constr_expr:
  | e=additive_expr { e }

indexes:
  | i = index { i }
  | i1=index COMMA i2=indexes { List.app i1 i2 }

index:
  | { [Iall] }
  | COLON { [Iall] }
  | e=expr { [Isingle e] }
  | e=expr COLON { [Iupfrom e] }
  | COLON e=expr { [Idownfrom e] }
  | e1=expr COLON e2=expr { [Ibetween e1 e2] }

printables:
  | p = printable { p }
  | p1=printable COMMA p2=printables { List.app p1 p2 }

printable:
  | e=expr { [Pexpr e] }
  | s=string_literal { [Pstring s] }

(* L-values *)
lhs:
  | id=identifier { Evar id }
  | l=lhs LBRACK indices=indexes RBRACK { Eindexed l indices }

(* statements *)
statement:
  | s=closed_statement { s }
  | s=open_statement { s }

atomic_statement:
  | l=lhs op=assignment_op e=expr SEMICOLON { Sassign l op e }
  | id=identifier LPAREN args=separated_list(COMMA, expr) RPAREN SEMICOLON { Scall id args }
  | e=expr TILDE id=identifier LPAREN es=separated_list(COMMA, expr) RPAREN ot=option(truncation) SEMICOLON
    { Stilde e id es (match ot with | Some tt_ => tt_ | None => (None,None) end) }
  | TARGET PLUSASSIGN e=expr SEMICOLON { Starget e }
  | BREAK SEMICOLON { Sbreak }
  | CONTINUE SEMICOLON { Scontinue }
  | PRINT LPAREN l=printables RPAREN SEMICOLON { Sprint l }
  | REJECT LPAREN l=printables RPAREN SEMICOLON { Sreject l  }
  | RETURN e=expr SEMICOLON { Sreturn (Some e) }
  | RETURN SEMICOLON { Sreturn None }
  | SEMICOLON { Sskip }

assignment_op:
  | ASSIGN { None }
  | PLUSASSIGN { Some Plus }
  | MINUSASSIGN { Some Minus }
  | TIMESASSIGN { Some Times }
  | DIVIDEASSIGN { Some Divide }
  | ELTTIMESASSIGN { Some EltTimes }
  | ELTDIVIDEASSIGN { Some EltDivide  }

string_literal:
  | s=STRINGLITERAL { fst s }

truncation:
  | TRUNCATE LBRACK e1=option(expr) COMMA e2=option(expr) RBRACK { (e1,e2) }

open_statement:
  | IF_ LPAREN e=expr RPAREN s=simple_statement { Sifthenelse e s Sskip }
  | IF_ LPAREN e=expr RPAREN s=open_statement { Sifthenelse e s Sskip }
  | IF_ LPAREN e=expr RPAREN s1=closed_statement ELSE s2=open_statement { Sifthenelse e s1 s2 }
  | WHILE LPAREN e=expr RPAREN s=open_statement { Swhile e s }
  | FOR LPAREN id=identifier IN e1=expr COLON e2=expr RPAREN s=open_statement { Sfor id e1 e2 s }
  | FOR LPAREN id=identifier IN e=expr RPAREN s=open_statement { Sforeach id e s }

closed_statement:
  | IF_ LPAREN e=expr RPAREN s1=closed_statement ELSE s2=closed_statement { Sifthenelse e s1 s2 }
  | WHILE LPAREN e=expr RPAREN s=closed_statement { Swhile e s }
  | s=simple_statement { s }
  | FOR LPAREN id=identifier IN e1=expr COLON e2=expr RPAREN s=closed_statement { Sfor id e1 e2 s }
  | FOR LPAREN id=identifier IN e=expr RPAREN s=closed_statement { Sforeach id e s }

simple_statement:
  | LBRACE l=list(vardecl_or_statement)  RBRACE { Sblock l } 
  | s=atomic_statement { s }

(* statement or var decls *)
vardecl_or_statement:
  | s=statement { s }
  | v=var_decl { v }

top_vardecl_or_statement:
  | s=statement { s }
  | v=top_var_decl { v }
