# Driver's code

The code in Sparse drives the parser and performs the elaboration. The
elaboration translates the Stan programs coming out of the parser to
the Stanlight programs expected by the Backend. The key responsibility
of the elaboration is to declare all the global names to the compiler
and the linker. In CompCert, elaboration is roughly an identity
function with side effects that do not affect the semantics. In
ProbCompCert, for now, this is not true and we make sue of the
elaboration to perform type checking, filtering of unsupported
features, and some desugaring. Eventually, all of these should be
moved into the formally verified part of the compiler.

* [Sparse](driver/Sparse.ml): code that drives the parser and elaborates the compiled
  program. Currently, Sparse also performs type checking and some
  syntax desugaring. 
* [Sstanlib](driver/Sparse.ml): elaboration of the standard library

# Generation of supporting code

During elaboration, we also generate C code that is then used by the
final program. This includes utilities to print and read structures,
and utilities for the proposal function. Note that doing the proposal
in an unverified way does not affect the correctness of the generated
code. Errors in the proposal are only an engineering concern and might
lead to slower convergence.

* [Sprelude](driver/Sparse.ml): generation of the structures and utilities for the parameters and the data. 
* [Spropose](driver/Sparse.ml): generation of the proposal function. 
