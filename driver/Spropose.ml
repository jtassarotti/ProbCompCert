exception NIY_propose of string

let renderPropose global_state struct_type struct_vars =
  let proposeField (var, p, t) =
    let v = Camlcoq.extern_atom p in
    match (t, var.Stan.vd_dims) with
    | (t, [])                   ->
      "  " ^ (String.concat "\n  " [
          "eps = my_randn(0.0,1.0);";
           "c->" ^ v ^" = s->" ^ v ^" + eps;";
      ])
    | _ -> raise (NIY_propose "renderPropose.proposeField: incomplete for this type")
  in
  String.concat "\n" ([
"double my_randn (double mu, double sigma)";
"{";
"  double U1, U2, W, mult;";
"  static double X1, X2;";
"  static int call = 0;";
"";
"  if (call == 1)";
"    {";
"      call = !call;";
"      return (mu + sigma * (double) X2);";
"    }";
"  do";
"    {";
"      U1 = -1 + ((double) rand () / RAND_MAX) * 2;";
"      U2 = -1 + ((double) rand () / RAND_MAX) * 2;";
"      W = pow (U1, 2) + pow (U2, 2);";
"    }";
"  while (W >= 1 || W == 0);";
"";
"  mult = sqrt ((-2 * log (W)) / W);";
"  X1 = U1 * mult;";
"  X2 = U2 * mult;";
"";
"  call = !call;";
"" ;
"  return (mu + sigma * (double) X1);";
"}";
    ("void* propose (void * opaque_state) {");
    ("  struct " ^ struct_type ^ "* s = (struct " ^ struct_type ^ "*) opaque_state;");
    ("  struct " ^ struct_type ^ "* c = malloc(sizeof (struct " ^ struct_type ^ "));");
    ("double eps;")
  ] @ (List.map proposeField struct_vars) @ [
    ("  return c;");
    "}";
    "";
  ])
