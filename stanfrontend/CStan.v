(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)


Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Stan.
Require Import SimplExpr.

Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)       (*FIXME: I think we can remove this *)
  | Econst_float: float -> type -> expr   (**r double float literal *)
  | Econst_single: float32 -> type -> expr (**r single float literal *) (*FIXME: I think we can remove this *)
  | Econst_long: int64 -> type -> expr    (**r long integer literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Ecast: expr -> type -> expr           (**r type cast ([(ty) e]) *)
  | Efield: expr -> ident -> type -> expr (**r access to a member of a struct or union *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Esizeof: type -> type -> expr         (**r size of a type *)
  | Ealignof: type -> type -> expr        (**r alignment of a type *)
  | Etarget: type -> expr.

Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty => ty
  | Econst_float _ ty => ty
  | Econst_single _ ty => ty
  | Econst_long _ ty => ty
  | Evar _ ty => ty
  | Etempvar _ ty => ty
  | Ederef _ ty => ty
  | Eaddrof _ ty => ty
  | Ecast _ ty => ty
  | Efield _ _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Esizeof _ ty => ty
  | Ealignof _ ty => ty
  | Etarget ty => ty
  end.

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Starget: expr -> statement              (**r target += expr *)
  | Stilde: expr -> expr -> list expr -> (option expr * option expr) -> statement
                      (**r expr ~ expr(list expr) T[option exr, option expr] *)

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)

Definition Swhile (e: expr) (s: statement) :=
  Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

Definition Sdowhile (s: statement) (e: expr) :=
  Sloop s (Sifthenelse e Sskip Sbreak).

Definition Sfor
  (s1: statement) (* initializing statement *)
  (e2: expr) (* conditional *)
  (s3: statement) (* body *)
  (s4: statement) (* postprocessing statement *)
  := Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).

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

Inductive blocktype
  := BTModel
  | BTParameters
  | BTData
  | BTGetState | BTSetState
  | BTPropose
  | BTPrintState | BTPrintData | BTSetData
  | BTOther.

Record function := mkfunction {
  fn_return: Ctypes.type;
  fn_params: list (ident * Ctypes.type);
  fn_body: statement;
  fn_blocktype: blocktype;
  fn_generator: SimplExpr.generator;
  fn_callconv: calling_convention;
  fn_temps: list (ident * Ctypes.type);
  fn_vars: list (ident * Ctypes.type);
}.

Definition var_names (vars: list(ident * Ctypes.type)) : list ident :=
  List.map (@fst ident Ctypes.type) vars.

Definition fundef := Ctypes.fundef function.

Definition type_of_function (f: function) : Ctypes.type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : Ctypes.type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

Inductive math_func := MFLog | MFExp | MFLogit | MFExpit
                       | MFPrintStart
                       | MFPrintDouble
                       | MFPrintInt
                       | MFPrintArrayInt
                       | MFPrintEnd
                       | MFInitUnconstrained.
Definition math_func_eq_dec : forall (x y : math_func), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.

Inductive dist_func := DBernPMF | DUnifPDF.
Definition dist_func_eq_dec : forall (x y : dist_func), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.

Record reserved_params := mkreserved_params {
  res_params_type: AST.ident;
  res_params_global_state: AST.ident;
  res_params_global_proposal: AST.ident;
  res_params_arg: AST.ident; (* arguments may not be in the temp list and, therefore, cannot be trivially added through gensym *)
}.
Record reserved_data := mkreserved_data {
  res_data_type: AST.ident;
  res_data_global: AST.ident;
  res_data_arg: AST.ident; (* arguments may not be in the temp list and, therefore, cannot be trivially added through gensym *)
}.

Record program : Type := {
  prog_defs: list (ident * globdef fundef type);
  prog_public: list ident;
  prog_main: ident;
  prog_model: ident;
  prog_constraints: list (ident * constraint);
  prog_parameters: ident;
  prog_parameters_vars: list (ident * type);
  prog_parameters_struct: reserved_params;
  prog_transformed_parameters: ident;
  prog_data: ident;
  prog_data_vars: list (ident * type);
  prog_data_struct: reserved_data;
  prog_transformed_data: ident;
  prog_generated_quantities: ident;
  prog_types: list composite_definition;
  prog_comp_env: composite_env;
  prog_comp_env_eq: build_composite_env prog_types = OK prog_comp_env;
  prog_math_functions: list (math_func * ident * Ctypes.type);
  prog_dist_functions: list (dist_func * ident);
}.

Definition program_of_program (p: program) : AST.program fundef type :=
  {| AST.prog_defs := p.(prog_defs);
     AST.prog_public := p.(prog_public);
     AST.prog_main := p.(prog_main) |}.

Coercion program_of_program: program >-> AST.program.

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.

Definition globalenv (p: program) :=
  {| genv_genv := Genv.globalenv p; genv_cenv := p.(prog_comp_env) |}.

Definition env := PTree.t (block * Ctypes.type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * Ctypes.type)).

(** The temporary environment maps local temporaries to values. *)

Definition temp_env := PTree.t val.

Inductive deref_loc (ty: Ctypes.type) (m: mem) (b: block) (ofs: ptrofs) : val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs (Vptr b ofs).

Inductive assign_loc (ce: composite_env) (ty: Ctypes.type) (m: mem) (b: block) (ofs: ptrofs):
                                            val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce ty m b ofs (Vptr b' ofs') m'.

