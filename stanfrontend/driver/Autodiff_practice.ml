(*approximate value of Euler's constant e*)
let approx_e =
  let rec factorial n =
    match n with
    | 0. -> 1.
    | m -> m *. factorial (m -. 1.)
  in
  let rec find_e accuracy sum =
    match accuracy with
    | 0. -> sum +. 1.
    | m -> find_e (accuracy -. 1.) (sum +. (1. /. factorial accuracy))
  in
  find_e 100. 0.

type arith_op = Plus | Minus | Multiply | Divide | Power
type bool_op = And | Or | Equals
type func_op = Sigmoid

type expression =
  | Constant of float
  | Variable of string
  | Arith_Expression of expression * arith_op * expression
  | Func_Expression of expression * func_op
  | Bool_Expression of expression * bool_op * expression

type statement =
  | Empty_statement
  | Assign of expression * expression
  | Sequence of statement * statement
  | If_then_else of expression * statement * statement
  | For_loop of expression * expression * expression * statement
  | While_loop of expression * statement

(*arith_op -> string*)
let string_arith_op op =
  match op with
  | Plus -> " + "
  | Minus -> " - "
  | Multiply -> " * "
  | Divide -> " / "
  | Power -> " ^ "

(*bool_op -> string*)
let string_bool_op op =
  match op with
  | And -> " && "
  | Or -> " || "
  | Equals -> " == "

(*expression -> string*)
let rec string_expr expr =
  match expr with
  | Constant value -> string_of_float value
  | Variable name -> name
  | Arith_Expression (expr1, op, expr2) ->
    String.concat "" ["("; string_expr expr1; string_arith_op op; string_expr expr2; ")"]
  | Func_Expression (expr, op) ->
    begin
      match op with
      | Sigmoid -> "1/(1+e^(-" ^ (string_expr expr) ^ "))"
    end
  | Bool_Expression (expr1, op, expr2) ->
    String.concat "" ["("; string_expr expr1; string_bool_op op; string_expr expr2; ")"]

(*statement -> string*)
let rec string_statement stmt =
  match stmt with
  | Empty_statement -> ""
  | Assign (expr1, expr2) -> String.concat "" [string_expr expr1; " = "; string_expr expr2; "\n"]
  | Sequence (stmt1, stmt2) -> (string_statement stmt1) ^ (string_statement stmt2)
  | If_then_else (expr, stmt1, stmt2) ->
    String.concat "" [string_expr expr; " ? "; string_statement stmt1; " : "; string_statement stmt2; ";\n"]
  | For_loop (var, init, final, stmt) ->
    String.concat "" ["for ("; string_expr var; " in "; string_expr init; ":"; string_expr final; ") {\n"; string_statement stmt; "}\n"]
  | While_loop (expr, stmt) ->
    String.concat "" ["while ("; string_expr expr; ") {\n"; string_statement stmt; "}\n"]

(*functions for dealing with lists of Assign statements*)

(*statement -> expr * expr
  given an Assign statement, gives the two expressions
  that are being set equal to each other in Assign statement*)
let unpack_assign assign =
  match assign with
  | Assign (var, expr) -> (var, expr)
  | _ -> (Constant 0., Constant 0.)

(*expression -> statement list -> expression
  given a variable and list of Assign statements,
  gives the corresponding expression for that variable*)
let rec get_expr var var_assignments =
  match var_assignments with
  | [] -> Constant 0.
  | assign :: ls ->
    begin
      let (this_var, this_expr) = unpack_assign assign in
      match var = this_var with
      | true -> this_expr
      | false -> get_expr var ls
    end

(* expression -> expression -> statement list -> statement list
   given a variable, an expression, and a list of Assign statements,
   gives back a new list with where the Assign statement with that variable
  now holds the given expression*)
let rec set_expr var expr var_assignments =
  match var_assignments with
  | [] -> [Assign (var, expr)]
  | assign :: ls ->
    begin
      let (this_var, this_expr) = unpack_assign assign in
      match var = this_var with
      | true -> (Assign (var, expr) :: ls)
      | false -> assign :: ls
    end

(*expression -> statement list -> bool
  given a variable and a list of Assign statements,
  returns whether the list has a statement with that variable*)
let rec has_var_assignment var var_assignments =
  match var_assignments with
  | [] -> false
  | assign :: ls ->
    begin
      let (this_var, this_expr) = unpack_assign assign in
      match var = this_var with
      | true -> true
      | false -> has_var_assignment var ls
    end

(*expression -> statement list -> expression
  given an expression and a list of Assign statements,
  substitutes in all the variables it can in expression
  from the Assign statements given*)
let rec fill_in_vars expr var_list =
  match expr with
  | Constant _ -> expr
  | Variable name ->
    begin
      let var_equiv_expr = get_expr expr var_list in
      match var_equiv_expr with
      | Constant _ -> expr
      | _ -> var_equiv_expr
    end
  | Arith_Expression (expr1, op, expr2) -> Arith_Expression ((fill_in_vars expr1 var_list), op, (fill_in_vars expr2 var_list))
  | Func_Expression (expr, Sigmoid) -> Func_Expression ((fill_in_vars expr var_list), Sigmoid)
  | Bool_Expression (expr1, op, expr2) -> Bool_Expression ((fill_in_vars expr1 var_list), op, (fill_in_vars expr2 var_list))

(*statement list -> string*)
let rec string_assignments var_assignments =
  match var_assignments with
  | [] -> "\n"
  | assign :: ls -> (string_statement assign) ^ string_assignments ls

(*expression -> statement list -> float
  gives the floating point value of an expression
  statement list will be made of of Assign statements giving values of variables*)
let rec evaluate expr var_val_list =
  match expr with
  | Constant value -> value
  | Variable _ -> evaluate (get_expr expr var_val_list) var_val_list
  | Arith_Expression (expr1, Plus, expr2) -> (evaluate expr1 var_val_list) +. evaluate expr2 var_val_list
  | Arith_Expression (expr1, Minus, expr2) -> (evaluate expr1 var_val_list) -. evaluate expr2 var_val_list
  | Arith_Expression (expr1, Multiply, expr2) -> (evaluate expr1 var_val_list) *. evaluate expr2 var_val_list
  | Arith_Expression (expr1, Divide, expr2) -> (evaluate expr1 var_val_list) /. evaluate expr2 var_val_list
  | Arith_Expression (expr1, Power, expr2) -> (evaluate expr1 var_val_list) ** evaluate expr2 var_val_list
  | Func_Expression (expr, Sigmoid) -> 1. /. (1. +. approx_e ** (-1. *. evaluate expr var_val_list))
  | Bool_Expression (expr1, And, expr2) ->
    begin
      match (evaluate expr1 var_val_list) +. (evaluate expr2 var_val_list) with
      | 2. -> 1.
      | _ -> 0.
    end
  | Bool_Expression (expr1, Or, expr2) ->
    begin
      match (evaluate expr1 var_val_list) +. (evaluate expr2 var_val_list) with
      | 0. -> 0.
      | _ -> 1.
    end
  | Bool_Expression (expr1, Equals, expr2) ->
    begin
      match expr1 = expr2 with
      | true -> 1.
      | false -> 0.
    end

    (*expression -> expression -> expression*)
(* expr will be an expression, sub_expr will be one of its sub-expressions*)
let differentiate_wrt expr sub_expr =
  match expr with
  | Constant value -> Constant 0.
  | Variable name ->
    begin
      match sub_expr = expr with
      | true -> Constant 1.
      | false -> Constant 0.
    end
  | Arith_Expression (expr1, Plus, expr2) ->
    begin
      match (sub_expr = expr1, sub_expr = expr2) with
      | (true, true) -> Constant 2.
      | (true, false) -> Constant 1.
      | (false, true) -> Constant 1.
      | _ -> Constant 0.
    end
  | Arith_Expression (expr1, Minus, expr2) ->
    begin
      match (sub_expr = expr1, sub_expr = expr2) with
     | (true, true) -> Constant 0.
     | (true, false) -> Constant 1.
     | (false, true) -> Constant (-1.)
     | _ -> Constant 0.
    end
  | Arith_Expression (expr1, Multiply, expr2) ->
    begin
     match (sub_expr = expr1, sub_expr = expr2) with
     | (true, true) -> Arith_Expression (Constant 2., Multiply, sub_expr)
     | (true, false) -> expr2
     | (false, true) -> expr1
     | _ -> Constant 0.
   end
  | Arith_Expression (expr1, Divide, expr2) ->
    begin
      match (sub_expr = expr1, sub_expr = expr2) with
      | (true, true) -> Constant 0.
      | (true, false) -> Arith_Expression (Constant 1., Divide, expr2)
      | (false, true) ->
         Arith_Expression (Arith_Expression (Constant (-1.), Multiply, expr1), Divide, Arith_Expression (expr2, Power, Constant 2.))
      | _ -> Constant 0.
    end
  | Arith_Expression (expr1, Power, expr2) ->
    begin
      match sub_expr with
      | expr1 -> Arith_Expression (expr2, Multiply, Arith_Expression (expr1, Power, (Arith_Expression (expr2, Minus, Constant 1.))))
    end
  | Func_Expression (expr, Sigmoid) ->
    begin
      match sub_expr = expr with
      | true ->
       Arith_Expression (Func_Expression (expr, Sigmoid), Multiply, Arith_Expression (Constant 1., Minus, Func_Expression (expr, Sigmoid)))
      | false -> Constant 0.
    end
  | Bool_Expression (_,_,_) -> Constant 0.

(*expression -> expression *)
(* reverse differentiation
   for sub_expression v_i with children expressions v_j and v_k,
   adjoint v_i = adjoint v_k * dv_k/dv_i + adjoint v_j * dv_j/dv_i*)
(* recurse on current_expr
   prev_derivs should start out as
   Constant 1. then df/v_3 then df/v_3 * dv_3/v_2 then df/v_3 * dv_3/v_2 * dv_2/v_1
   where v_1 = target_expr*)
let rec diff_back_wrt current_expr target_var prev_derivs =
  match current_expr with
  | Arith_Expression (expr1, _, expr2) ->
    begin
      let deriv1 = differentiate_wrt current_expr expr1 in
      let new_derivs1 = Arith_Expression (prev_derivs, Multiply, deriv1) in
      let diff_back1 = diff_back_wrt expr1 target_var new_derivs1 in
      match expr1 = expr2 with
      | true -> diff_back1
      | false ->
        begin
          let deriv2 = differentiate_wrt current_expr expr2 in
          let new_derivs2 = Arith_Expression (prev_derivs, Multiply, deriv2) in
          let diff_back2 = diff_back_wrt expr2 target_var new_derivs2 in
          Arith_Expression (diff_back1, Plus, diff_back2)
        end
    end
  | Func_Expression (expr, Sigmoid) ->
    let deriv = differentiate_wrt current_expr expr in
    let new_derivs = Arith_Expression (prev_derivs, Multiply, deriv) in
    diff_back_wrt expr target_var new_derivs
  | _ ->(*Constants and Variables*)
    let deriv = differentiate_wrt current_expr target_var in
    Arith_Expression(prev_derivs, Multiply, deriv)

(*expression -> expression -> expression*)
(*forward differentiation*)
let rec diff_forward_wrt current_expr target_expr =
  match current_expr with
  | Arith_Expression (expr1, op, expr2) ->
    begin
      let deriv1 = diff_forward_wrt expr1 target_expr in
      let deriv2 = diff_forward_wrt expr2 target_expr in
      begin
        match op with
        | Plus -> Arith_Expression (deriv1, Plus, deriv2)
        | Minus -> Arith_Expression (deriv1, Minus, deriv2)
        | Multiply -> Arith_Expression (Arith_Expression (expr1, Multiply, deriv2), Plus, Arith_Expression (deriv1, Multiply, expr2))
        | Divide -> (*ho dhi - hi dho / ho^2*)
          Arith_Expression (Arith_Expression (Arith_Expression (expr2, Multiply, deriv1), Minus, Arith_Expression(expr1, Multiply, deriv2)), Divide, Arith_Expression (expr2, Multiply, expr2))
        | Power ->
          Arith_Expression (deriv1, Multiply, Arith_Expression (expr2, Multiply, Arith_Expression (expr1, Power, Arith_Expression (expr2, Minus, Constant 1.))))
      end
    end
  | Func_Expression (expr, Sigmoid) -> Constant 0.
  | _ -> (*Constants and Variables*)
    begin
      let deriv = differentiate_wrt current_expr target_expr in
      deriv
    end

(*statement -> statement list -> expression * statement list*)
  (*given a statement and a list of Assign statements,
  returns expression-version of statement as well as list of all the variable assignments
  recurses on stmt
  assume code looked like
  stmt_1
  stmt_2
  ...stmt_n
  and the statement object looks like Sequence (Sequence (Sequence stmt1 stmt2) stmt3) stmt4*)
let rec stmt_to_expr stmt var_list =
  match stmt with
  | Empty_statement -> (Constant 0., var_list)
  | Assign (var, expr) ->
    begin
      match has_var_assignment var var_list with
      | true ->
        begin
          let new_var_list = set_expr var expr var_list in
          let new_expr = fill_in_vars expr var_list in
          (new_expr, new_var_list)
        end
      | false ->
        begin
          let new_expr = fill_in_vars expr var_list in
          let new_var_list = (Assign (var, new_expr)) :: var_list in
          (new_expr, new_var_list)
        end
    end
  | Sequence (stmt1, stmt2) ->
    begin
      let (new_expr1, new_var_list1) = stmt_to_expr stmt1 var_list in
      stmt_to_expr stmt2 new_var_list1
    end
  | If_then_else (expr, stmt1, stmt2) ->
    begin
      let conditional = evaluate expr var_list in
      match conditional with
      | 1. -> stmt_to_expr stmt1 var_list
      | _ -> stmt_to_expr stmt2 var_list
    end
  | For_loop (identifier, expr2, expr3, stmt1) ->
    begin
      let begin_val = Float.to_int (evaluate expr2 var_list) in
      let end_val = Float.to_int (evaluate expr3 var_list) in
      let answer = ref (expr2, Assign (identifier, expr2) :: var_list) in
      for i = begin_val to end_val do
        let (_, new_var_list) = !answer in
        let modified_var_list = set_expr identifier (Constant (float_of_int i)) new_var_list in
        answer := (stmt_to_expr stmt1 modified_var_list)
      done;
      !answer
    end
  | While_loop (expr, stmt1) -> (Constant 0., var_list)
(*can't get the code beneath to run*)
      (*
      begin
        let conditional = ref (evaluate expr var_list) in
        let answer = ref (expr, var_list) in
        while !conditional = 1. do
          let (_, new_var_list) = !answer in
          answer := stmt_to_expr stmt1 new_var_list;
          conditional := evalutate expr new_var_list
        done
        !answer
      end
      *)

let main =
  let x = Variable "x" in
  let y = Variable "y" in
  let z = Variable "z" in
  let var_values = [Assign (x, Constant 4.); Assign (y, Constant 5.); Assign (z, Constant 6.)] in
  let _ = print_string (string_assignments var_values) in
  let stmt1 = Assign (Variable "w", Arith_Expression (x, Multiply, x)) in
  let stmt2 = Assign (Variable "u", Arith_Expression (Variable "w", Divide, y)) in
  let stmt3 = Sequence (stmt1, stmt2) in
  let _ = print_string (string_statement stmt3 ^ "\n") in
  let (expr2, new_var_list) = stmt_to_expr stmt3 var_values in
  let _ = print_string (string_expr expr2 ^ "\n") in

  let _ = print_string ("\ndifferentiating backwards: \n") in
  let deriv_back_wrt_x = diff_back_wrt expr2 x (Constant 1.) in
  let _ = print_string ("du/dx = " ^ string_expr deriv_back_wrt_x ^ "\n") in
  let deriv_back_val = evaluate deriv_back_wrt_x var_values in
  let _ = print_string (string_of_float deriv_back_val ^ "\n") in

  let _ = print_string ("\ndifferentiating forwards: \n") in
  let deriv_for_wrt_x = diff_forward_wrt expr2 x in
  let _ = print_string ("du/dx = " ^ string_expr deriv_for_wrt_x ^ "\n") in
  let deriv_for_val = evaluate deriv_for_wrt_x var_values in
  print_string (string_of_float deriv_for_val ^ "\n")
