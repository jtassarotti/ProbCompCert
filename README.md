# ProbCompCert

The ProbCompCert compiler is a prototype compiler for a subset of the
Stan programming that ties into the CompCert C compiler.

The distinguishing feature of ProbCompCert is that parts of it are being
formally verified using the Coq proof assistant. The goal is for the
generated assembly code is formally guaranteed to behave as prescribed
by the semantics of the source Stan code.

ProbCompCert is derived from CompCert. With the exception of the files
in the stanfrontend directory, all files are subject to
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

We try to keep ProbCompCert's modifications to CompCert
separated. Most of ProbCompCert's files can be found in the
[stanfrontend](stanfrontend) directory, which contains a [description
of the compiler's architecture](stanfrontend/README.md). There are a
few exceptions where the Stan extensions must integrate with CompCert
in files outside that subdirectory:

* [driver](driver/Driver.ml): compiler's entrypoint, extended to know what to do with stan programs
* [Makefile](Makefile): ProbcompCert's Coq files need to be listed here
* [Makefile.extr](Makefile.extr): Makefile to build the final executable
* [extraction](extraction/extraction.v): extended to handle the generation of compiler for stan inputs

Notes to developers:

* In general, you do not need to edit the driver or the extraction
* You only need to modify Makefile.extr if you want to add plain Caml code in new directories. Such directories need to be declared so that the OCaml build tools know where to look for code
* If you add new Coq file in stanfrontend, it needs to be listed in the Makefile, and order does matter

See more information in
[stanfrontend/README.md](stanfrontend/README.md) and
[stanfrontend/DEVELOPERS.md](stanfrontend/DEVELOPERS.md)