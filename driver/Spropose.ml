exception NIY_propose of string

let generate_proposal global_state struct_type struct_vars =
  let proposeField (var, p, t) =
    let v = Camlcoq.extern_atom p in
    match (t, var.Stan.vd_dims) with
    | (t, [])                   ->
      "  " ^ (String.concat "\n  " [
          "eps = randn(0.0,1.0);";
           "c->" ^ v ^" = s->" ^ v ^" + eps;";
      ])
    | _ -> raise (NIY_propose "renderPropose.proposeField: incomplete for this type")
  in
  String.concat "\n" ([
    ("void* propose (void * opaque_state) {");
    ("  struct " ^ struct_type ^ "* s = (struct " ^ struct_type ^ "*) opaque_state;");
    ("  struct " ^ struct_type ^ "* c = malloc(sizeof (struct " ^ struct_type ^ "));");
    ("double eps;")
      ] @ (List.map proposeField struct_vars) @ [
    ("  return c;");
    "}";
    "";
  ])
