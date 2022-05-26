# General information

ProbCompCert ties directly into CompCert by generating Clight code and
makes heavy use of most of the generic compiler libraries of CompCert
including: Coqlib, Maps, Integers, Floats, Errors, AST, Linking,
Values, Memory, Globalenvs, Smallstep, Op, Ctypes, and Clight.

Documentation on these libraries can be found in [CompCert's commented
Coq development](https://compcert.org/doc/index.html)

The [runtime](runtime) directory contains the C implementation of the
runtime and of the standard library.

The [tests](tests) directory contains Stan example programs and
development tools.

# Commented Coq development

# Languages, syntax and semantics:

* [Stan](Stan.v)

* [Stanlight](Stanlight.v)

* [CStan](CStan.v)

# Parsing

# Compiler passes

# All together