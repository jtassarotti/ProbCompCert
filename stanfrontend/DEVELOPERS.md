This document describes some useful points for those who want to
modify the ProbCompCert source.

For installation instructions, see `INSTALL.md`. For general
usage of ProbCompCert, see `USAGE.md`

## Overview of files

The root of the repository mostly contains CompCert files. We will
refer to this root directory as "ProbCompCert/". The Stan specific
code for ProbCompCert is found in the ProbCompCert/stanfrontend/
subdirectory. Here are some important files in this subdirectory:

- `Stanlight.v` : this gives the syntax of the Stanlight language
  being compiled

- `Ssemantics.v` : operational and denotational semantics of Stanlight
  (Section 3 of the paper), also includes statement of semantic
  refinement (Section 4.1)

- `StanEnv.v` : axioms about real numbers and the Stan "math"
  functions that need to be called (See the paragraph "Floating Points
  and Reals" on p. 9 of the paper)

- `DenotationalSimulation.v` : General proofs about operational
  simulations preserving denotational semantics

- `Sampling.v`, `Samplingproof.v` : definition of the sampling pass
  and its proof of preservation

- `Reparameterization.v`, `Reparameterizationproof.v` : reparam pass
  and proof (Section 5)

- `AdditiveConst.v`, `AdditiveConstproof.v` : the additive const pass
  and proof (Section 6)

- `Scompiler.v` : definition of the entire compiler function
  (including unverified passes + CompCert C light passes), transitive
  proof of preservation for the 3 verified stanlight passes
  (transf_stanlight_program_denotational_preserved)

- `tests/bench/` : the various benchmark programs used in the paper. 

- `runtime/` : the C files for the "runtime" used by ProbCompCert
  generated programs. This includes the MCMC driver loop, the math
  libraries, a 3rd party JSON parser used to handle parsing
  data/parameter initialization files.

- `driver/` : Stan specific OCaml code used for elaboration before Coq
  compilation and non-verified generation of auxiliary code
  (e.g. proposal generators). See also the ProbCompcert/driver
  subdirectory (i.e. the driver directory at the root of the
  repository), which contains analogous OCaml code for CompCert
  itself.

## Extending the Compiler

For adding additional unverified passes to the compiler at the OCaml
level, code can be hooked into `process_stan_file` and
`compile_stan_file` in `ProbCompCert/driver/Driver.ml`.

For adding Coq passes, add the relevant pass to `transf_stan_program`
or `transf_stan_program_complete` in
`ProbCompCert/stanfrontend/Scompiler.v`. The latter is the function
that is extracted called by the OCaml Driver.ml code as part of
`compile_stan_file`.

## Extending the Standard Library

To add a new distribution or mathematical function to the standard
library, there are 3 steps.

1) Add the C signature for the function to
`ProbCompCert/stanfrontend/runtime/stanlib.h`.

2) Add the implementation of the function to
`ProbCompCert/stanfrontend/runtime/stanlib.c`.

3) Add the function and its signature to the list
`library_math_functions` in
`ProbCompCert/stanfrontend/driver/Sstanlib.ml`.

For example, suppose we wanted to add the `lognormal`
distribution. Then, we would apply the following changes, which we
list here in `patch` notation:

```
--- a/stanfrontend/driver/Sstanlib.ml
+++ b/stanfrontend/driver/Sstanlib.ml
@@ -25,6 +25,9 @@ let library_math_functions = [
     "normal_lpdf",
     tdouble,
     [tdouble; tdouble; tdouble];
+    "lognormal_lpdf",
+    tdouble,
+    [tdouble; tdouble; tdouble];
     "normal_lupdf",
     tdouble,
     [tdouble; tdouble; tdouble];

--- a/stanfrontend/runtime/stanlib.c
+++ b/stanfrontend/runtime/stanlib.c
@@ -91,6 +91,11 @@ double normal_lupdf(double x, double mean, double sigma)
   return (- log(sigma) - (pow((x-mean)/sigma,2) / 2));
 }
 
+double lognormal_lpdf(double x, double mean, double sigma)
+{
+  return normal_lpdf(log(x), mean, sigma);
+}
+
 double bernoulli_lpmf(int x, double p)
 {
     /* printf("bernoulli_lpmf(%d, %f)\n", x, p); */

--- a/stanfrontend/runtime/stanlib.h
+++ b/stanfrontend/runtime/stanlib.h
@@ -16,6 +16,7 @@ double uniform_lpdf(double x, double a, double b);
 double uniform_lpmf(int x, double a, double b);
 double normal_lpdf(double x, double mean, double stddev);
 double normal_lupdf(double x, double mean, double stddev);
+double lognormal_lpdf(double x, double mean, double stddev);
 double bernoulli_lpmf(int x, double p);
 double cauchy_lpdf(double x, double location, double scale);
 double cauchy_lupdf(double x, double location, double scale);
```

Re-make the compiler, and then it should be possible to use
`lognormal_lpdf` as a function that is called, as well as using
`lognormal` in Stan's sampling notation, as in a statement like `mu ~
lognormal(mu, sigma)`.

In particular, the OCaml elaborator, when it encounters `mu ~
lognormal(mu, sigma)` will automatically elaborate this to `mu ~
lognormal_lpdf(mu, sigma)` in the `Stanlight` AST (it searches for
either a `_lpdf` or `_lpmf` variant in the list of functions declared
in `Sstanlib.ml` and uses whichever it finds).

Note that the `AdditiveConst.v` optimization pass can also be extended
to remap `lognormal_lpdf` to `lognormal_lupdf` (if we had also added
the latter). However, that is a more substantial under taking as we
would also have to define the semantics of `lognormal_lpdf` and
`lognormal_lupdf` in `StanEnv.v` and prove that they differ by only an
additive constant.