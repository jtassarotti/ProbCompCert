# ProbCompCert
The formally-verified Stan compiler.

## Overview
The ProbCompCert verified compiler is a prototype compiler for a subset of the
Stan programming that ties into the CompCert C compiler.

The distinguishing feature of ProbCompCert is that it is being formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source Stan code.

ProbCompCert is derived from CompCert. With the exception of the files
in the stanfrontend directory and the files in the driver directory
whose filename starts with an uppercase S, all files are subject to
CompCert's licensing and copyright rules, as explained below. 

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support and extra features, can be purchased from
[AbsInt](https://www.absint.com).  See the file `LICENSE` for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.


## Architecture of ProbCompCert

The part of ProbCompcert that is formally verified can be found in the
stanfrontend directory, which contains a description of the compiler's
architecture.

The compiler also relies on the following unverified code that can be
found in driver:

* Sparse.ml: code that drives the parser and elaborates the compiled
  program. Currently, Sparse also performs type checking and some
  syntax desugaring. 

* Sprelude.ml: generation of the structures and utilities for the parameters and the data. 

* Spropose.ml: generation of the proposal function. 

* Sstanlib.ml: declarationelaboration of the standard library
