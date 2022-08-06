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

(*
let rec string_uop uop =
  match uop with
  | Stanlight.PNot -> " ! "
  | _ -> ""
what do you mean PNot is unbound???*)

let rec basic_to_string bas =
  match bas with
  | Stanlight.Bint -> "int"
  | Stanlight.Breal -> "real"
  | Stanlight.Barray (basic, intgrs) -> (basic_to_string basic) ^ "[" ^ Camlcoq.Z.to_string intgrs ^ "]"
  | Stanlight.Bfunction (basiclist, basic) -> "inputs -> " ^ (basic_to_string basic)

(*uniform_lpdf and bernoulli_lpdf are both variables???*)
let rec expression_to_string expr =
  match expr with
  | Stanlight.Econst_int (intgr, bas) -> Camlcoq.Z.to_string intgr
  | Stanlight.Econst_float (flt, bas) -> string_of_float (Camlcoq.camlfloat_of_coqfloat flt)
  | Stanlight.Evar (ident, bas) -> Camlcoq.extern_atom ident
  | Stanlight.Ecall (expr1, exprl, bas) -> String.concat "" ["Call "; expression_to_string expr1; "("; exprlist_to_string exprl; ")"]
  | Stanlight.Eunop (expr1, bas) -> "not " ^ expression_to_string expr1
  | Stanlight.Ebinop (expr1, b_op, expr2, bas) -> String.concat "" [expression_to_string expr1; op_to_string b_op; expression_to_string expr2]
  | Stanlight.Eindexed (expr1, exprl, bas) -> String.concat "" [expression_to_string expr1; "["; exprlist_to_string exprl; "]"]
  | Stanlight.Etarget bas -> "target" (*what is this??*)
and exprlist_to_string exprlist =
  match exprlist with
  | Stanlight.Enil -> ""
  | Stanlight.Econs (e, Stanlight.Enil) -> expression_to_string e
  | Stanlight.Econs (e, es) -> String.concat "" [expression_to_string e; ", "; exprlist_to_string es]


let rec statement_to_string stmt =
  match stmt with
  | Stanlight.Sskip -> ""
  | Stanlight.Sassign (expr1, opr, expr2) -> String.concat "" [expression_to_string expr1; " = "; expression_to_string expr2; ";\n"] (*how to incorporate option part of option_op??*)
  | Stanlight.Ssequence (stmt1, stmt2) -> statement_to_string stmt1 ^ statement_to_string stmt2
  | Stanlight.Sifthenelse (expr, stmt1, stmt2) -> String.concat "" [expression_to_string expr; " ? "; statement_to_string stmt1; " : "; statement_to_string stmt2; ";\n"]
  | Stanlight.Sfor (ident, expr1, expr2, stmt1) -> String.concat "" ["for ("; Camlcoq.extern_atom ident; " in "; expression_to_string expr1; ":"; expression_to_string expr2; ") {\n"; statement_to_string stmt1; "}\n"]
  | Stanlight.Starget expr -> String.concat "" ["target += "; expression_to_string expr; ";\n"]
  | Stanlight.Stilde (expr1, expr2, exprl) -> String.concat "" [expression_to_string expr1; " ~ "; expression_to_string expr2; "("; exprlist_to_string exprl; ")"; ";\n"]

(*expression -> expression -> expression*)
let diff_wrt expr sub_expr =
  let zero_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 0., Stanlight.Breal) in
  let one_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 1., Stanlight.Breal) in
  let two_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat 2., Stanlight.Breal) in
  let neg_one_float = Stanlight.Econst_float (Camlcoq.coqfloat_of_camlfloat (-1.), Stanlight.Breal) in
  match expr with
  | Stanlight.Econst_int (_, _) -> zero_float
  | Stanlight.Econst_float (_, _) -> zero_float
  | Stanlight.Evar (_, bas) ->
    begin
      match sub_expr = expr with
      | true -> one_float
      | false -> zero_float
    end
  | Stanlight.Ecall (_,_,_)-> zero_float (*figure out what this is*)
  | Stanlight.Eunop (_,_) -> zero_float
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
  | Stanlight.Eindexed (_, _, _) -> zero_float
  | Stanlight.Etarget _ -> zero_float

(*helper functions for dealing with list of Sassigns*)

(*expression -> statement list -> expression*)
let rec get_expr variable variable_assignments =
  match variable_assignments with
  | [] -> variable
  | Stanlight.Sassign (expr1, opr, expr2) :: ls ->
  begin
    match variable = expr1 with
    | true -> expr2
    | false -> get_expr variable ls
  end
  | _ -> variable

(*expression -> expression -> statement list -> statement list*)
let rec set_expr variable expression variable_assignments =
  match variable_assignments with
  | [] -> []
  | Stanlight.Sassign (expr1, opr, expr2) :: ls ->
    begin
      match variable = expr1 with
      | true -> Stanlight.Sassign (expr1, opr, expression) :: ls
      | false -> Stanlight.Sassign (expr1, opr, expr2) :: (set_expr variable expression ls)
    end
  | _ -> variable_assignments

(*expression -> statement list -> bool*)
let rec has_var_assignment variable variable_assignments =
  match variable_assignments with
  | [] -> false
  | Stanlight.Sassign (expr1, opr, expr2) :: ls ->
    begin
      match variable = expr1 with
      | true -> true
      | false -> has_var_assignment variable ls
    end
  | _ -> false

let bool_to_float bool_val =
  match bool_val with
  | true -> 1.
  | false -> 0.

(*expression -> statement list -> float*)
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
  | Stanlight.Eindexed (expr1, exprl, bas) -> 0. (*fill in*)
  | Stanlight.Etarget bas -> 0. (*fill in*)


(*actually going through the program definitions to hunt down model*)

let fundef_to_funcbody fdf =
  match fdf with
  | Ctypes.Internal f -> f.Stanlight.fn_body
  | Ctypes.External _ -> Stanlight.Sskip

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

let rec program_defs gbs =
  match gbs with
  | (ident, _) :: gs -> String.concat "\n" [Camlcoq.extern_atom ident; program_defs gs]
  | _ -> ""

let generate_proposal program =
  let programdefs = program.Stanlight.pr_defs in
  let stmt = programdefs_to_funcbody programdefs "model" in
  let _ = print_string (statement_to_string stmt ^ "\n") in
  let pro = generate_prologue () in
  let epi = generate_epilogue () in
  let body = String.concat "\n" (List.map generate_param program.Stanlight.pr_parameters_vars) in
  String.concat "\n" [pro; body; ""; epi]
