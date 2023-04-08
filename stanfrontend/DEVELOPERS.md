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