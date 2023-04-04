(** * Syntax of the Stanlight language.

  This is a simplified subset of Stan that is the input to the
  verified section of ProbCompCert compiler. Features supported
  include arrays, 1-dimensional constraints.

  Stan's built-ins for various mathematical operations and
  distributions are not modeled as primitive parts of the
  syntax. Instead, these are modeled as function calls from an
  enviroment.

  See Ssemantics.v for the semantics.

*)


Require Import Integers.
Require Import Coqlib.
Require Import Floats.
Require Import AST.
Require Import Globalenvs. 
Require Ctypes. 

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
  | Ecast: expr -> basic -> expr           (**r type cast ([(ty) e]) *)
  | Ecall: expr -> exprlist -> basic -> expr
  | Eunop: u_op -> expr -> basic -> expr
  | Ebinop: expr -> b_op -> expr -> basic -> expr
  | Eindexed: expr -> exprlist -> basic -> expr (**r indexing into an array e[e1,...,en] of type ty *)
  | Etarget: basic -> expr                      (**r accessing the value of the target variable *)
with exprlist :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.


Inductive constraint :=
  | Cidentity                         (**r no constraint *)
  | Clower: float -> constraint       (**r <lower=r> *)
  | Cupper: float -> constraint       (**r <upper=r> *)
  | Clower_upper: float -> float -> constraint. (**r <lower=r1, upper=r2> *)

Inductive statement :=
  | Sskip : statement
  | Sassign : expr -> option b_op -> expr -> statement
  | Ssequence: statement -> statement -> statement
  | Sifthenelse: expr -> statement -> statement -> statement
  | Sfor: ident -> expr -> expr -> statement -> statement
  | Starget: expr -> statement                     (**r add to target variable, target += e *)
  | Stilde: expr -> expr -> exprlist -> statement. (**r sampling statements, e1 ~ e2(es) *)

Record variable := mkvariable {
  vd_type: basic;
  vd_constraint: constraint;
}.

Record function := mkfunction {
  fn_body: statement;
  fn_vars: list (ident * basic);
}.

Definition fundef := Ctypes.fundef function.

(* A Stanlight program consists of:
   - pr_defs: definitions of all of identifiers (globals, parameters, data vars, functions, etc. Compare
     with the "prog_defs" field of CompCert's AST.program record.
   - pr_parameters_vars: Listing of designated "parameter" variables and "output maps" expr -> expr
   - pr_data_vars: Listing of the designated "data" variables *)

(* TODO : it is probably better to not includ ethe "basic" field of
   the pr_parameters/data_vars in this record, since the information is
   therefore redundant across the definitions of these variables in
   pr_defs *)

Record program := mkprogram {
  pr_defs: list (ident * globdef fundef variable);
  (* Last part of tuple is an expression showing how to map a paramter from internal representation to
     user displayable output *)
  pr_parameters_vars: list (ident * basic * option (expr -> expr));
  pr_data_vars: list (ident * basic);
}.

(* Many CompCert libraries assume "programs" are of the AST.program
   type which designates a list of definitions, a list of public
   identifiers, and the identifier of the "main" function.  That does
   not quite make sense for a Stanlight program, but it is
   nevertheless useful to be able to map a Stanlight program to an
   AST.program by filling in trivial definitions for public/main *)

Definition program_of_program (p: program) : AST.program fundef variable :=
  {| AST.prog_defs := p.(pr_defs);
     AST.prog_public := nil;
     AST.prog_main := xH |}.

Coercion program_of_program: program >-> AST.program.

(* Constructing a CompCert globalenv from the program by adding all
   defs to an empty environment *)

Definition globalenv (p: program) :=
   Genv.add_globals (Genv.empty_genv fundef variable nil) p.(prog_defs).


Fixpoint count_down_ofs (n: nat) :=
  match n with
  | O => nil
  | S n' => (Ptrofs.repr (Z.of_nat (S n'))) :: count_down_ofs n'
  end.

Definition count_up_ofs (n: nat) := rev (count_down_ofs n).

Fixpoint count_up_ofs_aux (start: nat) (n: nat) :=
  match n with
  | O => nil
  | S n' => (Ptrofs.repr (Z.of_nat start)) :: count_up_ofs_aux (S start) n'
  end.

Lemma count_up_ofs_aux_S_r st n :
  count_up_ofs_aux st (S n) = count_up_ofs_aux st n ++ ((Ptrofs.repr (Z.of_nat (st + n))) :: nil).
Proof.
  revert st.
  induction n; intros st; simpl; auto.
  { repeat f_equal; lia. }
  { simpl in IHn. replace (st + S n)%nat with (S (st + n)) by lia.
    rewrite <-IHn. auto.
  }
Qed.

Lemma count_up_ofs_equiv n :
  count_up_ofs n = count_up_ofs_aux 1 n.
Proof.
  induction n.
  { simpl; auto. }
  { simpl. unfold count_up_ofs. simpl. unfold count_up_ofs in IHn. rewrite IHn.
    rewrite <-count_up_ofs_aux_S_r. auto.
  }
Qed.

Fixpoint count_down_int (n: nat) : list Integers.Int.int :=
  match n with
  | O => nil
  | S n' => (Int.repr (Z.of_nat (S n'))) :: count_down_int n'
  end.

Definition count_up_int (n: nat) := rev (count_down_int n).

Fixpoint count_up_int_aux (start: nat) (n: nat) :=
  match n with
  | O => nil
  | S n' => (Int.repr (Z.of_nat start)) :: count_up_int_aux (S start) n'
  end.

Lemma count_up_int_aux_S_r st n :
  count_up_int_aux st (S n) = count_up_int_aux st n ++ ((Int.repr (Z.of_nat (st + n))) :: nil).
Proof.
  revert st.
  induction n; intros st; simpl; auto.
  { repeat f_equal; lia. }
  { simpl in IHn. replace (st + S n)%nat with (S (st + n)) by lia.
    rewrite <-IHn. auto.
  }
Qed.

Lemma count_up_int_equiv n :
  count_up_int n = count_up_int_aux (S O) n.
Proof.
  induction n.
  { simpl; auto. }
  { simpl. unfold count_up_int. simpl. unfold count_up_int in IHn. rewrite IHn.
    rewrite <-count_up_int_aux_S_r. auto.
  }
Qed.

Definition typeof (e: expr) : basic :=
  match e with
  | Econst_int _ ty => ty
  | Econst_float _ ty => ty
  | Evar _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Ecall e el ty => ty
  | Eindexed e el ty => ty
  | Etarget ty => ty
  | Ecast _ ty => ty
  end.
