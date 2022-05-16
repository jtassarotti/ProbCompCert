open List
   
exception NIY_stanlib of string

let sizeof_basic t =
  begin match t with
  | StanE.Bint -> 4l
  | StanE.Breal -> 8l
  | StanE.Barray (ty, n) -> Int32.mul 8l  (Camlcoq.camlint_of_coqint n)
  | _ -> raise (Invalid_argument "Sparse does not calculate the size of this type")
  end

let sizeof_struct vars =
  List.fold_left (fun total var -> Int32.add total (sizeof_basic (snd var))) 0l vars

let init_int = AST.Init_space (Camlcoq.coqint_of_camlint 4l)
let init_dbl = AST.Init_space (Camlcoq.coqint_of_camlint 8l)
let init_ptr = AST.Init_space (Camlcoq.coqint_of_camlint 8l)
let init_struct members = AST.Init_space (Camlcoq.coqint_of_camlint (sizeof_struct members))

let ctarray (t, sz) = Ctypes.Tarray (t, sz, Ctypes.noattr) (* FIXME defined in Clightdefs *)
let tdouble = Stypes.Treal
let bdouble = StanE.Breal
let ctdouble = Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr) (* FIXME defined in Clightdefs *)
let tint = Stypes.Tint
let bint = StanE.Bint
let ctint = Ctypes.Tint (Ctypes.I32, Ctypes.Signed, Ctypes.noattr) (* FIXME defined in Clightdefs *)
let rt = Some tdouble
let to_charlist s = List.init (String.length s) (String.get s)
let ftype = Ctypes.Tfunction (Ctypes.Tnil, (Ctypes.Tfloat (Ctypes.F64, Ctypes.noattr)), AST.cc_default)

let ast_to_ctype x =
  match x with
  | AST.Tfloat -> ctdouble
  | AST.Tint -> ctint
  | _ -> raise (NIY_stanlib "ast_to_ctype: incomplete for this type")

let mk_ctypelist xs =
  List.fold_left (fun tail h -> Ctypes.Tcons (h, tail)) Ctypes.Tnil xs

let mk_ctypelist_from_astlist xs =
    mk_ctypelist (List.rev (List.map ast_to_ctype xs))

let mk_cfunc xs = Ctypes.Tfunction (mk_ctypelist_from_astlist xs, ctdouble, AST.cc_default)

let mk_global_func ret str ast_args_list =
    AST.Gfun (Ctypes.External
       (AST.EF_external
          (to_charlist str, {
            AST.sig_args=ast_args_list;
            AST.sig_res=ret;
            AST.sig_cc=AST.cc_default;
          }),
       mk_ctypelist_from_astlist ast_args_list,
       ctdouble,
       AST.cc_default
    ))

let mk_global_math_func = mk_global_func (AST.Tret AST.Tfloat)


                        
let st_uniform_lpdf = "uniform_lpdf"
let id_uniform_lpdf = Camlcoq.intern_string st_uniform_lpdf
let ty_uniform_lpdf = StanE.Bfunction (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, StanE.Bnil))))), bdouble)
let gl_uniform_lpdf = mk_global_math_func st_uniform_lpdf [AST.Tfloat; AST.Tfloat; AST.Tfloat]

let st_normal_lpdf = "normal_lpdf"
let id_normal_lpdf = Camlcoq.intern_string st_normal_lpdf
let ty_normal_lpdf = StanE.Bfunction (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, StanE.Bnil))))), bdouble)
let gl_normal_lpdf = mk_global_math_func st_normal_lpdf [AST.Tfloat; AST.Tfloat; AST.Tfloat]                    

let st_cauchy_lpdf = "cauchy_lpdf"
let id_cauchy_lpdf = Camlcoq.intern_string st_cauchy_lpdf
let ty_cauchy_lpdf = StanE.Bfunction (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, (StanE.Bcons (bdouble, StanE.Bnil))))), bdouble)
let gl_cauchy_lpdf = mk_global_math_func st_cauchy_lpdf [AST.Tfloat; AST.Tfloat; AST.Tfloat]  

let st_exponential_lpdf = "exponential_lpdf"
let id_exponential_lpdf = Camlcoq.intern_string st_exponential_lpdf
let ty_exponential_lpdf = StanE.Bfunction (StanE.Bcons (bdouble,  (StanE.Bcons (bdouble, StanE.Bnil))), bdouble)
let gl_exponential_lpdf = mk_global_math_func st_exponential_lpdf [AST.Tfloat; AST.Tfloat] 
                   
let st_bernoulli_lpmf = "bernoulli_lpmf"
let id_bernoulli_lpmf = Camlcoq.intern_string st_bernoulli_lpmf
let ty_bernoulli_lpmf = StanE.Bfunction (StanE.Bcons (bint, (StanE.Bcons (bdouble, StanE.Bnil))), bdouble)
let gl_bernoulli_lpmf = mk_global_math_func st_bernoulli_lpmf [AST.Tint; AST.Tfloat]

let st_poisson_lpmf = "poisson_lpmf"
let id_poisson_lpmf = Camlcoq.intern_string st_poisson_lpmf
let ty_poisson_lpmf = StanE.Bfunction (StanE.Bcons (bint, (StanE.Bcons (bdouble, StanE.Bnil))), bdouble)
let gl_poisson_lpmf = mk_global_math_func st_poisson_lpmf [AST.Tint; AST.Tfloat]                      

let st_bernoulli_logit_lpmf = "bernoulli_logit_lpmf"
let id_bernoulli_logit_lpmf = Camlcoq.intern_string st_bernoulli_logit_lpmf
let ty_bernoulli_logit_lpmf = StanE.Bfunction (StanE.Bcons (bint, (StanE.Bcons (bdouble, StanE.Bnil))), bdouble)
let gl_bernoulli_logit_lpmf = mk_global_math_func st_bernoulli_logit_lpmf [AST.Tint; AST.Tfloat]                      

let transf_dist_idents = Hashtbl.create 3;;
Hashtbl.add transf_dist_idents "uniform" (id_uniform_lpdf, ty_uniform_lpdf);
Hashtbl.add transf_dist_idents "bernoulli" (id_bernoulli_lpmf, ty_bernoulli_lpmf);
Hashtbl.add transf_dist_idents "poisson" (id_poisson_lpmf, ty_poisson_lpmf);
Hashtbl.add transf_dist_idents "bernoulli_logit" (id_bernoulli_logit_lpmf, ty_bernoulli_logit_lpmf);
Hashtbl.add transf_dist_idents "normal" (id_normal_lpdf, ty_normal_lpdf);
Hashtbl.add transf_dist_idents "cauchy" (id_cauchy_lpdf, ty_cauchy_lpdf);
Hashtbl.add transf_dist_idents "exponential" (id_exponential_lpdf, ty_exponential_lpdf)
let stanlib_functions = [
    (id_uniform_lpdf,   gl_uniform_lpdf);
    (id_bernoulli_lpmf, gl_bernoulli_lpmf);
    (id_normal_lpdf, gl_normal_lpdf);
    (id_cauchy_lpdf, gl_cauchy_lpdf);
    (id_poisson_lpmf, gl_poisson_lpmf);
    (id_bernoulli_logit_lpmf, gl_bernoulli_logit_lpmf);
    (id_exponential_lpdf, gl_exponential_lpdf)
  ]
let pr_dist_functions = [(CStan.DBernPMF, id_bernoulli_lpmf);(CStan.DUnifPDF, id_uniform_lpdf)]

(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
(*                              math functions                                  *)
(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)

let _ = Camlcoq.use_canonical_atoms := true
                      
let mk_fn ret args s =
  (*
  let p = Camlcoq.intern_string s in
  print_string s;
  print_string ": ";
  print_string (Int64.to_string (Camlcoq.P.to_int64 p));
  print_string "\n";
  flush(stdout);
   *)
  (s, Camlcoq.intern_string s, mk_global_func ret s args, mk_cfunc args)
let mk_math_fn = mk_fn (AST.Tret AST.Tfloat)
let mk_unary_math_fn t = mk_math_fn [t]
let unary_math_fn = mk_unary_math_fn AST.Tfloat

let (st_log, id_log, gl_log, clog)       = unary_math_fn "log"
let (st_exp, id_exp, gl_exp, cexp)       = unary_math_fn "exp"
let (st_logit, id_logit, gl_logit, clogit) = unary_math_fn "logit"
let (st_expit, id_expit, gl_expit, cexpit) = unary_math_fn "expit"
let (st_sqrt, id_sqrt, gl_sqrt, csqrt) = unary_math_fn "sqrt"

let __math_functions = [ (id_log, gl_log, clog);
                         (id_logit, gl_logit, clogit);
                         (id_exp, gl_exp, cexp);
                         (id_expit, gl_expit, cexpit);
                         (id_sqrt, gl_sqrt, csqrt);
                        ]

let _as_prog_math_functions (i, g, c) = (i, c)
let _as_global_math_functions (i, g, c) = (i, g)

let pr_math_functions = List.map _as_prog_math_functions __math_functions
let all_math_fns = List.map _as_global_math_functions __math_functions




