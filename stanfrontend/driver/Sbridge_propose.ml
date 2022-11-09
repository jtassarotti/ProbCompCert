exception NIY_propose of string

let generate_prologue () =
  String.concat "\n" [
      "void propose (double * state, double * candidate) {";
      "  double eps;";
      ""
    ]

let generate_epilogue () =
  String.concat "\n" [
      "}";
      ""
    ]

let generate_param (ofs, ((id, t), f)) =
  match t with
  | Stanlight.Breal -> String.concat "\n" [
                   "  eps = randn(0.0,1.0);";
                   "  candidate[" ^ (string_of_int ofs) ^"] = state[" ^ (string_of_int ofs) ^"] + eps;";
                     ]
  | Stanlight.Barray (Stanlight.Breal,sz) -> String.concat "\n" [
                                         "  for (int i = 0; i < " ^ (Camlcoq.Z.to_string sz) ^ " ; i++) {";
                                         "    eps = randn(0.0,1.0);";
                                         "    candidate[" ^ (string_of_int ofs) ^ "+i] = state[" ^ (string_of_int ofs) ^ "+i] + eps;";
                                         "  }";
                                       ]
  | _ -> raise (NIY_propose "Not handling non-real types yet")
      
let generate_proposal program =
  let sz_one ((_, typ), _) =
    match typ with
    | Stanlight.Barray (_, sz) -> (Camlcoq.Z.to_int  sz)
    | _ -> 1
  in

  let rec gen_ofs (start : int) ls =
    match ls with
    | [] -> []
    | x :: ls ->
       ((start, x) :: (gen_ofs ((sz_one x) + start) ls))
  in

  let params = program.Stanlight.pr_parameters_vars in
  let params_ofs = gen_ofs 0 params in

  let pro = generate_prologue () in
  let epi = generate_epilogue () in
  let body = String.concat "\n" (List.map generate_param params_ofs) in
  String.concat "\n" [pro; body; ""; epi]
