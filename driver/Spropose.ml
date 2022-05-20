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
  | StanE.Breal -> String.concat "\n" [
                   "  eps = randn(0.0,1.0);";
                   "  candidate->" ^ name ^" = state->" ^ name ^" + eps;";
                     ]
  | StanE.Barray (StanE.Breal,sz) -> String.concat "\n" [
                                         "  for (int i = 0; i < " ^ (Camlcoq.Z.to_string sz) ^ " ; i++) {";
                                         "    eps = randn(0.0,1.0);";
                                         "    candidate->" ^ name ^ "[i]" ^ " = state->" ^ name ^ "[i]" ^" + eps;";
                                         "  }";
                                       ]
  | _ -> raise (NIY_propose "Not handling non-real types yet")
      
let generate_proposal program =
  let pro = generate_prologue () in
  let epi = generate_epilogue () in
  let body = String.concat "\n" (List.map generate_param program.StanE.pr_parameters_vars) in
  String.concat "\n" [pro; body; ""; epi]
