exception NIY_propose of string

let generate_prologue () =
  String.concat "\n" [
      "void* propose (void * opaque_state) {";
      "  struct Params* s = (struct Params*) opaque_state;";
      "  struct Params* c = malloc(sizeof (struct Params));";
      "  double eps;";
      ""
    ]

let generate_epilogue () =
  String.concat "\n" [
      "  return c;";
      "}";
      ""
    ]

let generate_param (id, t) =
  let name = Camlcoq.extern_atom id in
  let t = Hashtbl.find Sparse.type_table name in
  match t with
  | StanE.Breal -> String.concat "\n" [
                   "  eps = randn(0.0,1.0);";
                   "  c->" ^ name ^" = s->" ^ name ^" + eps;";
                 ]
  | _ -> raise (NIY_propose "Not handling non-real types yet")
      
let generate_proposal program =
  let pro = generate_prologue () in
  let epi = generate_epilogue () in
  let body = String.concat "\n" (List.map generate_param program.StanE.pr_parameters_vars) in
  String.concat "\n" [pro; body; ""; epi]
