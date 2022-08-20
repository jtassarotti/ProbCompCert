exception NIY_propose of string

let generate_prologue () =
  String.concat "\n" [
      "void propose (struct Params* state, struct Params* candidate) {";
      "  double eps;";
      ""
    ]

let generate_epilogue () =
  String.concat "\n" [
      "}";
      ""
    ]

let generate_param (id, t) =
  let name = Camlcoq.extern_atom id in
  match t with
  | Stanlight.Breal -> String.concat "\n" [
                   "  eps = randn(0.0,1.0);";
                   "  candidate->" ^ name ^" = state->" ^ name ^" + eps;";
                     ]
  | Stanlight.Barray (Stanlight.Breal,sz) -> String.concat "\n" [
                                         "  for (int i = 0; i < " ^ (Camlcoq.Z.to_string sz) ^ " ; i++) {";
                                         "    eps = randn(0.0,1.0);";
                                         "    candidate->" ^ name ^ "[i]" ^ " = state->" ^ name ^ "[i]" ^" + eps;";
                                         "  }";
                                       ]
  | _ -> raise (NIY_propose "Not handling non-real types yet")

(*functions for converting op, basic, expression, statement types to string*)
let op_to_string b_op =
  match b_op with
  | Stanlight.Plus -> " + "
  | Stanlight.Minus -> " - "
  | Stanlight.Times -> " * "
  | Stanlight.Divide -> " / "
  | Stanlight.Modulo -> " % "
  | Stanlight.Or -> " || "
  | Stanlight.And -> " && "
  | Stanlight.Equals -> " == "
  | Stanlight.NEquals -> " != "
  | Stanlight.Less -> " < "
  | Stanlight.Leq -> " <= "
  | Stanlight.Greater -> " > "
  | Stanlight.Geq -> " >= "

let rec basic_to_string bas =
  match bas with
  | Stanlight.Bint -> "int"
  | Stanlight.Breal -> "real"
  | Stanlight.Barray (basic, intgrs) -> (basic_to_string basic) ^ "[" ^ Camlcoq.Z.to_string intgrs ^ "]"
  | Stanlight.Bfunction (basiclist, basic) -> (basic_to_string basic)

let rec expr_to_string expr =
  match expr with
  | Stanlight.Econst_int (intgr, bas) -> Camlcoq.Z.to_string intgr
  | Stanlight.Econst_float (flt, bas) -> string_of_float (Camlcoq.camlfloat_of_coqfloat flt)
  | Stanlight.Evar (ident, bas) -> basic_to_string bas ^ " " ^ Camlcoq.extern_atom ident
  | Stanlight.Ecall (expr1, exprl, bas) -> String.concat "" [expr_to_string expr1; "("; exprlist_to_string exprl; ")"]
  | Stanlight.Eunop (expr1, bas) -> "not " ^ expr_to_string expr1
  | Stanlight.Ebinop (expr1, b_op, expr2, bas) -> String.concat "" ["("; expr_to_string expr1; op_to_string b_op; expr_to_string expr2; ")"]
  | Stanlight.Eindexed (expr1, exprl, bas) -> String.concat "" [expr_to_string expr1; "["; exprlist_to_string exprl; "]"]
  | Stanlight.Etarget bas -> "target" (*what is this??*)
and exprlist_to_string exprlist =
  match exprlist with
  | Stanlight.Enil -> ""
  | Stanlight.Econs (e, Stanlight.Enil) -> expr_to_string e
  | Stanlight.Econs (e, es) -> String.concat "" [expr_to_string e; ", "; exprlist_to_string es]

let rec statement_to_string stmt =
  match stmt with
  | Stanlight.Sskip -> ""
  | Stanlight.Sassign (expr1, opr, expr2) ->
    begin
      match opr with
      | None -> String.concat "" [expr_to_string expr1; " = "; expr_to_string expr2; ";\n"]
      | Some biop -> String.concat "" [expr_to_string expr1; op_to_string biop; expr_to_string expr2; ";\n"]
    end
  | Stanlight.Ssequence (stmt1, stmt2) -> statement_to_string stmt1 ^ statement_to_string stmt2
  | Stanlight.Sifthenelse (expr, stmt1, stmt2) -> String.concat "" ["if "; expr_to_string expr; " {\n"; statement_to_string stmt1; "}\nelse {\n"; statement_to_string stmt2; "}\n"]
  | Stanlight.Sfor (ident, expr1, expr2, stmt1) -> String.concat "" ["for ("; Camlcoq.extern_atom ident; " in "; expr_to_string expr1; ":"; expr_to_string expr2; ") {\n"; statement_to_string stmt1; "}\n"]
  | Stanlight.Starget expr -> String.concat "" ["target += "; expr_to_string expr; ";\n"]
  | Stanlight.Stilde (expr1, expr2, exprl) -> String.concat "" [expr_to_string expr1; " ~ "; expr_to_string expr2; "("; exprlist_to_string exprl; ")"; ";\n"]

(*Autodiff*)

(*expression -> expression -> expression
differentiates expr with respect to sub_expr and returns result as an expression
when derivative is equal to a constant, returns it as an Econst_float
assumes that if expr is Ebinop (expr1, op, expr2, bas) and sub_expr is not expr1 or expr2, then expr1 and expr2 are not in terms of sub_expr
*)
let diff_wrt expr sub_expr =
  let zero_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 0., Stanlight.Breal) in
  let one_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 1., Stanlight.Breal) in
  let two_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 2., Stanlight.Breal) in
  let neg_one_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat (-1.), Stanlight.Breal) in
  match expr with
  | Stanlight.Econst_int (_, _) ->
    begin
      match sub_expr = expr with
      | true -> one_float
      | false -> zero_float
    end
  | Stanlight.Econst_float (_, _) ->
    begin
      match sub_expr = expr with
      | true -> one_float
      | false -> zero_float
    end
  | Stanlight.Evar (_, bas) ->
    begin
      match sub_expr = expr with
      | true -> one_float
      | false -> zero_float
    end
  | Stanlight.Ecall (_,_,_)-> zero_float (*figure out what this is*)
  | Stanlight.Eunop (_,_) ->
    begin
      match sub_expr = expr with
      | true -> neg_one_float
      | false -> zero_float
    end
  | Stanlight.Ebinop (expr1, op, expr2, bas) ->
    begin
      match op with
      | Stanlight.Plus ->
        begin
          match (expr1 = sub_expr, expr2 = sub_expr) with
          | (true, true) -> two_float
          | (true, false) -> one_float
          | (false, true) -> one_float
          | (false, false) -> zero_float
        end
      | Stanlight.Minus ->
        begin
          match (expr1 = sub_expr, expr2 = sub_expr) with
          | (true, true) -> zero_float
          | (true, false) -> one_float
          | (false, true) -> neg_one_float
          | (false, false) -> zero_float
        end
      | Stanlight.Times ->
        begin
          match (expr1 = sub_expr, expr2 = sub_expr) with
          | (true, true) -> Stanlight.Ebinop (expr1, Stanlight.Times, two_float, bas)
          | (true, false) -> expr2
          | (false, true) -> expr1
          | (false, false) -> zero_float
        end
      | Stanlight.Divide ->
        begin
          match (expr1 = sub_expr, expr2 = sub_expr) with
          | (true, true) -> zero_float
          | (true, false) -> Stanlight.Ebinop (one_float, Stanlight.Divide, expr2, bas)
          | (false, true) ->
            begin
              let minus_hi_dho = Stanlight.Ebinop (neg_one_float, Stanlight.Times, expr1, bas) in
              let ho_squared = Stanlight.Ebinop (expr2, Stanlight.Times, expr2, bas) in
              Stanlight.Ebinop (minus_hi_dho, Stanlight.Divide, ho_squared, bas)
            end
          | (false, false) -> zero_float
        end
      | _ -> zero_float (*figure out what to do with Modulo and logic operators*)
    end
  | _ -> zero_float (*figure out what to do with Eindexed, Etarget*)

(*helper function for printing/debugging purposes*)
let diff_to_string expr sub_expr =
  let diff = diff_wrt expr sub_expr in
  String.concat "" ["d("; expr_to_string expr; ")/d("; expr_to_string sub_expr; ") = "; expr_to_string diff]

(*expression -> expression -> expression
reverse autodiff
prev_derivs should be initially set to 1. in Econst_float format*)
let rec rev_diff expr wrt_expr prev_derivs =
  match expr with
  | Stanlight.Ebinop (expr1, _, expr2, Stanlight.Breal) ->
    begin
      let deriv1 = diff_wrt expr expr1 in
      let _ = print_string((diff_to_string expr1 wrt_expr) ^ "\n" ^ diff_to_string expr2 wrt_expr ^ "\n") in
      let new_derivs1 = Stanlight.Ebinop (prev_derivs, Stanlight.Times, deriv1, Stanlight.Breal) in
      let rev_diff1 = rev_diff expr1 wrt_expr new_derivs1 in
      match expr1 = expr2 with
      | true -> rev_diff1
      | false ->
        begin
          let deriv2 = diff_wrt expr expr2 in
          let new_derivs2 = Stanlight.Ebinop (prev_derivs, Stanlight.Times, deriv2, Stanlight.Breal) in
          let rev_diff2 = rev_diff expr2 wrt_expr new_derivs2 in
          Stanlight.Ebinop (rev_diff1, Stanlight.Plus, rev_diff2, Stanlight.Breal)
        end
    end
  | _ ->
    let deriv = diff_wrt expr wrt_expr in
    Stanlight.Ebinop (prev_derivs, Stanlight.Times, deriv, Stanlight.Breal)

(*helper functions for dealing with list of Sassigns*)

(*expression -> statement list -> expression
given an Evar var and a list of Sassigns var_assignments,
finds the object Stanlight.Sassign (var, opr, expr) and returns expr
doesn't account for cases where opr is not None*)
let rec get_expr var var_assignments =
  match var_assignments with
  | [] -> var
  | Stanlight.Sassign (expr1, opr, expr2) :: ls -> (*figure out how to account for cases where opr is not None*)
  begin
    match var = expr1 with
    | true -> expr2
    | false -> get_expr var ls
  end
  | _ -> var

(*expression -> statement list -> bool
given an Evar var and a list of Sassigns var_assignments,
returns whether or not there is an Sassign object Stanlight.Sassign(var, opr, expr)*)
let rec has_var_assignment var var_assignments =
  match var_assignments with
  | [] -> false
  | Stanlight.Sassign (expr1, opr, expr2) :: ls ->
    begin
      match var = expr1 with
      | true -> true
      | false -> has_var_assignment var ls
    end
  | _ -> false

(*expression -> expression -> statement list -> statement list
given an Evar var, an expression expr, and a list of Sassigns var_assignments,
returns var_assignments with Stanlight.Sassigns (var, None, expr) added to the right if var_assignments didn't have any statements involving var
or returns a modified version of var_assignments with Stanlight.Sassigns (var, opr, expr) if var_assignments already had Stanlight.Sassigns (var, opr, prev_expr)*)
let rec set_expr var expr var_assignments =
  match var_assignments with
  | [] -> [Stanlight.Sassign (var, None, expr)]
  | Stanlight.Sassign (expr1, opr, prev_expr) :: ls ->
    begin
      match var = expr1 with
      | true -> Stanlight.Sassign (expr1, opr, expr) :: ls
      | false -> Stanlight.Sassign (expr1, opr, prev_expr) :: (set_expr var expr ls)
    end
  | _ -> var_assignments

(*expression -> statement list -> expression
given an expression expr and list of Sassigns var_assignments,
substitutes all the variables in expr with their corresponding expressions in Sassigns
unless the corresponding expression is an Econst_int or Econst_float, in which case the variable is returned as itself*)
let rec vars_subst_expr expr var_assignments =
  match expr with
  | Stanlight.Econst_int (_, _) -> expr
  | Stanlight.Econst_float (_, _) -> expr
  | Stanlight.Evar (ident, bas) ->
    begin
      let var_equiv_expr = get_expr expr var_assignments in
      match var_equiv_expr with
      | Stanlight.Econst_int (_, _) -> expr
      | Stanlight.Econst_float (_, _) -> expr
      | _ -> var_equiv_expr
    end
  | Stanlight.Ecall (call, args, bas) -> expr (*fill in*)
  | Stanlight.Eunop (expr1, bas) -> Stanlight.Eunop (vars_subst_expr expr1 var_assignments, bas)
  | Stanlight.Ebinop (expr1, op, expr2, bas) -> Stanlight.Ebinop (vars_subst_expr expr1 var_assignments, op, vars_subst_expr expr2 var_assignments, bas)
  | Stanlight.Etarget bas -> expr (*fill in*)
  | Stanlight.Eindexed (expr, exprl, bas) -> expr (*figure out how to do this*) (* Stanlight.Eindexed (vars_subst_expr expr var_assignments, vars_subst_exprl exprl var_assignments, bas)
and vars_subst_exprl exprl var_assignments =
  match exprl with
  | Enil -> Enil
  | Econs (e, el) -> Econs (vars_subst_expr e var_assignments, vars_subst_exprl el var_assignments)
*)

let bool_to_float bool_val =
  match bool_val with
  | true -> 1.
  | false -> 0.

(*expression -> statement list -> float
var_assignments must be a list of Sassigns that assign constants to all the variables in expr*)
let rec evaluate expr var_assignments =
  match expr with
  | Stanlight.Econst_int (intgr, _) -> float_of_int (Camlcoq.Z.to_int intgr)
  | Stanlight.Econst_float (flt, _) -> Camlcoq.camlfloat_of_coqfloat flt
  | Stanlight.Evar (ident, _) -> evaluate (get_expr expr var_assignments) var_assignments
  | Stanlight.Ecall (expr1, exprl, bas) -> evaluate expr1 var_assignments (*fill in*)
  | Stanlight.Eunop (expr1, bas) -> evaluate expr1 var_assignments (*fill in*)
  | Stanlight.Ebinop (expr1, b_op, expr2, bas) ->
    begin
      let expr1_val = evaluate expr1 var_assignments in
      let expr2_val = evaluate expr2 var_assignments in
      match b_op with
      | Stanlight.Plus -> expr1_val +. expr2_val
      | Stanlight.Minus -> expr1_val -. expr2_val
      | Stanlight.Times -> expr1_val *. expr2_val
      | Stanlight.Divide -> expr1_val /. expr2_val
      | Stanlight.Modulo -> float_of_int ((int_of_float expr1_val) mod (int_of_float expr2_val))
      | Stanlight.Or -> (*assuming true -> 1. and false -> 0.*)
        begin
          match (expr1_val, expr2_val) with
          | (0., 0.) -> 0.
          | (_, _) -> 1.
        end
      | Stanlight.And ->
        begin
          match (expr1_val, expr2_val) with
          | (1., 1.) -> 1.
          | (_, _) -> 0.
        end
      | Stanlight.Equals -> bool_to_float (expr1_val = expr2_val)
      | Stanlight.NEquals -> bool_to_float (not (expr1_val = expr2_val))
      | Stanlight.Less -> bool_to_float (expr1_val < expr2_val)
      | Stanlight.Leq -> bool_to_float (expr1_val <= expr2_val)
      | Stanlight.Greater -> bool_to_float (expr1_val > expr2_val)
      | Stanlight.Geq -> bool_to_float (expr1_val >= expr2_val)
    end
  | Stanlight.Eindexed (expr1, exprl, bas) -> evaluate (get_expr expr var_assignments) var_assignments
  | Stanlight.Etarget bas -> 0. (*fill in*)

(*statement -> expression -> statement list -> expression * statement list
intially, expr set as any expression when this function is first called
*)
let rec statement_to_expr stmt expr var_assignments =
  match stmt with
  | Stanlight.Sskip -> (expr, var_assignments)
  | Stanlight.Sassign (expr1, op, expr2) ->
    begin
      match expr1 with
      | Stanlight.Evar (i, bas) ->
        begin
          let new_expr = vars_subst_expr expr2 var_assignments in
          let new_assignments = set_expr expr1 new_expr var_assignments in
          (new_expr, new_assignments)
        end
      | Stanlight.Eindexed (expr1, exprl, bas) -> (expr, var_assignments) (*add Eindexed*)
      | _ -> (expr, var_assignments) (*fill out after thinking more*)
    end
  | Stanlight.Ssequence (stmt1, stmt2) ->
    begin
      let (new_expr1, new_var_assignments) = statement_to_expr stmt1 expr var_assignments in
      statement_to_expr stmt2 new_expr1 new_var_assignments (*check order of Ssequence*)
    end
  | Stanlight.Sifthenelse (conditional, stmt1, stmt2) ->
    begin
      let conditional_val = evaluate conditional var_assignments in
      match conditional_val with
      | 1. -> statement_to_expr stmt1 expr var_assignments
      | _ -> statement_to_expr stmt2 expr var_assignments
    end
  | Stanlight.Sfor(ident, start, finish, stmt1) ->
    begin
      let start_val = Float.to_int (evaluate start var_assignments) in
      let finish_val = Float.to_int (evaluate finish var_assignments) in
      let counter = Stanlight.Evar (ident, Stanlight.Breal) in
      let answer = ref (start, (Stanlight.Sassign (counter, Some Stanlight.Equals, start)) :: var_assignments) in
      for i = start_val to finish_val do
        let (_, new_var_assignments) = !answer in
        let modified_var_assignments = set_expr counter (Stanlight.Econst_int (Camlcoq.Z.of_sint i, Stanlight.Bint)) new_var_assignments in
        answer := (statement_to_expr stmt1 expr modified_var_assignments)
      done;
      !answer
    end
  | Stanlight.Starget _ -> (expr, var_assignments) (*figure this out*)
  | Stanlight.Stilde (_, _, _) -> (expr, var_assignments) (*figure this out*)

(*helper functions to unpack a Stanlight program*)

(*fundef -> statement*)
let fundef_to_funcbody fdf =
  match fdf with
  | Ctypes.Internal f -> f.Stanlight.fn_body
  | Ctypes.External _ -> Stanlight.Sskip

(* (ident * globdef fundef variable) list -> string -> statement*)
let rec programdefs_to_funcbody gbs block_name =
  match gbs with
  | [] -> Stanlight.Sskip
  | (ident, AST.Gfun fundef) :: gs ->
    begin
      match (Camlcoq.extern_atom ident) = block_name with
      | true -> fundef_to_funcbody fundef
      | false -> programdefs_to_funcbody gs block_name
    end
  | (ident, AST.Gvar v) :: gs -> programdefs_to_funcbody gs block_name

let fundef_to_string fdf =
  match fdf with
  | Ctypes.Internal f -> statement_to_string f.Stanlight.fn_body
  | Ctypes.External _ -> ""

let generate_proposal program =
(*
  let x = Stanlight.Evar (Camlcoq.intern_string "x", Stanlight.Breal) in
  let y = Stanlight.Evar (Camlcoq.intern_string "y", Stanlight.Breal) in
  let expr1 = Stanlight.Ebinop (x, Stanlight.Divide, x, Stanlight.Breal) in
  let expr2 = Stanlight.Ebinop (x, Stanlight.Times, y, Stanlight.Breal) in
  let expr3 = Stanlight.Ebinop (expr1, Stanlight.Minus, expr2, Stanlight.Breal) in
  let _ = print_string(expr_to_string expr3 ^ "\n") in
  let diff = rev_diff expr3 x (Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 1., Stanlight.Breal)) in
  let _ = print_string(expr_to_string diff ^ "\n") in
*)
  let programdefs = program.Stanlight.pr_defs in
  let model_stmt = programdefs_to_funcbody programdefs "model" in
  let _ = print_string ("\n\tprinting the model block:\n" ^ statement_to_string model_stmt ^ "\n") in
  let one_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 1., Stanlight.Breal) in
  let mu_var = Stanlight.Evar(Camlcoq.intern_string "mu", Stanlight.Breal) in
  (*let mu_assign = Stanlight.Sassign(mu_var, None, Stanlight.Breal) in*)
  let (model_expr, assign_list) = statement_to_expr model_stmt mu_var [] in
  let _ = print_string("\n\texpression version of model block:\n" ^ expr_to_string model_expr ^ "\n") in
  let diff = rev_diff model_expr mu_var one_float in
  let _ = print_string ("\n\treverse autodiff on model block with respect to mu:\n" ^ expr_to_string diff ^ "\n") in
  let pro = generate_prologue () in
  let epi = generate_epilogue () in
  let body = String.concat "\n" (List.map generate_param program.Stanlight.pr_parameters_vars) in
  String.concat "\n" [pro; body; ""; epi]
