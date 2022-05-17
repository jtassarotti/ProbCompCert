open List
   
exception NIY_stanlib of string

let _ = Camlcoq.use_canonical_atoms := true

let tdouble = Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr)
let tint = Ctypes.Tint (Ctypes.I32, Ctypes.Signed, Ctypes.noattr)
let ctarray (t, sz) = Ctypes.Tarray (t, sz, Ctypes.noattr)
      
let library_math_functions = [
    "log",
    tdouble,
    [tdouble];
    "exp",
    tdouble,
    [tdouble];
    "logit",
    tdouble,
    [tdouble];
    "expit",
    tdouble,
    [tdouble];
    "sqrt",
    tdouble,
    [tdouble];
    "uniform_lpdf",
    tdouble,
    [tdouble; tdouble; tdouble];
    "normal_lpdf",
    tdouble,
    [tdouble; tdouble; tdouble];
    "cauchy_lpdf",
    tdouble,
    [tdouble; tdouble; tdouble];
    "exponential_lpdf",
    tdouble,
    [tdouble; tdouble];
    "bernoulli_lpmf",
    tdouble,
    [tint; tdouble];
    "poisson_lpmf",
    tdouble,
    [tint; tdouble];
    "bernoulli_logit_lpmf",
    tdouble,
    [tint; tdouble];
  ]
 
let mk_global_func ret str args =
  let tyargs =
    List.fold_right (fun t tl -> Ctypes.Tcons(t, tl)) args Ctypes.Tnil in
    AST.Gfun (Ctypes.External
       (AST.EF_external
          (List.init (String.length str) (String.get str), {
            AST.sig_args=Ctypes.typlist_of_typelist tyargs;
            AST.sig_res=Ctypes.rettype_of_type ret;
            AST.sig_cc=AST.cc_default;
          }),
       tyargs,
       ret,
       AST.cc_default
    ))
                           
let library_function_declaration (name, tyres, tyargs) =
  (Camlcoq.intern_string name, mk_global_func tyres name tyargs)
                   
let all_math_fns = List.map library_function_declaration library_math_functions

let convert_Ctypes_to_Stan ty =
  match ty with
  | Ctypes.Tfloat _ -> StanE.Breal
  | Ctypes.Tint _  -> StanE.Bint
  | _ -> raise (NIY_stanlib "Missing type conversion")
       
let rec search library name =
  match library with
  | [] -> raise (NIY_stanlib ("Missing function: " ^ name))
  | f :: l ->
     begin
     match f with
     | f_name, tyret, tyargs ->
        print_string ("Comparing: " ^ f_name ^ "\n");
        flush(stdout);
        if ((f_name = name) || (f_name = (name^"_lpdf")) || (f_name = (name^"_lpmf")))
                                then f else search l name
     end

let rec type_of_parameters tyargs =
  match tyargs with
  | [] -> StanE.Bnil
  | arg :: args -> StanE.Bcons (convert_Ctypes_to_Stan arg, type_of_parameters args)
    
let type_of_library_function name =
  let (f,tyret,tyargs) = search library_math_functions name in
  (f,StanE.Bfunction (type_of_parameters tyargs, convert_Ctypes_to_Stan tyret))



