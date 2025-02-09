# General information

The ProbCompCert compiler is a prototype compiler for a subset of the
Stan programming that ties into the CompCert C compiler.

The distinguishing feature of ProbCompCert is that parts of it are being
formally verified using the Coq proof assistant. The goal is for the
generated assembly code is formally guaranteed to behave as prescribed
by the semantics of the source Stan code.

So far, we have verified 3 passes in the density compilation pipeline.
These passes are interesting from a compiler correctness point of
view, because they involve changes that do *not* necessarily preserve
the "extensional" **operational** semantics of the program, but
nevertheless preserve the probability distribution that the programs
represent.

# Installation

Please see [INSTALL.md](INSTALL.md) for instructions on getting
ProbCompCert built.

# Usage

For a step-by-step walkthrough that explains how to compile a Stan
model, run the resulting binary, and analyze the generated output, please
see [USAGE.md](USAGE.md)

# Overview

ProbCompCert ties directly into CompCert by generating Clight code and
makes heavy use of most of the generic compiler libraries of CompCert
including: Coqlib, Maps, Integers, Floats, Errors, AST, Linking,
Values, Memory, Globalenvs, Smallstep, Op, Ctypes, and Clight.

Documentation on these libraries can be found in [CompCert's commented
Coq development](https://compcert.org/doc/index.html)

* The [runtime](runtime) directory contains the C implementation of the
runtime and of the standard library.

* The [tests](tests) directory contains Stan example programs and
development tools.

* The [driver](driver) contains plain OCaml code that is used during the
elaboration phase that connects the Stan language to the Stanlight
language.

# Commented Coq development

## Languages, syntax and semantics:

Similar to CompCert, the compiler makes use of multiple languages. In
CompCert, to a large extent, every syntax is asscociated with a single
semantics, and a compiler pass that removes a feature maps to a new
language. An exception is Clight which comes with two semantics.

In ProbCompCert, at least for now, several compiler pass remain in the
same language despite removing a feature. As a result, some languages
are associated with multiple semantics.

* Stan: The Stan language, generated by the parser. This language is
  (or at least should be) faithful to the official Stan specification.

* Stanlight: A subset of Stan describing valid Stan programs. In
   principle, any Stan program could be written in Stanlight. This
   language supports compiler transformation that are probabilistic in
   nature. Example include reparameterization. 

* CStan: Clight extended with an explicit target and a list of
  parameters and data variables. This languages supports compiler
  transformations that need to work at a lower level. Examples include
  the transformation of global variables into C structures or the
  initialization and return of the target.

| Language | Syntax | Semantics | Notes |
| -------- | ------ | --------- | ----- |
| Stan     | [Stan](Stan.v)  |  | Does not currently have a formal semantics |
| Stanlight| [Stanlight](Stanlight.v) | [Ssemantics.v](Ssemantics.v) | Stanlight programs are valid Stan programs |
| CStan    | [CStan](CStan.v) | [CStanSemanticsTarget](CStanSemanticsTarget.v) [CStanSemanticsBackend](CStanSemanticsBackend.v)| CStan programs use the C type system and global environment|

## Parsing

The parser uses Menhir's verified parsing tools. The verified parser
was largely developed by Brian Ward as part of his [honor's
thesis](https://www.bc.edu/content/dam/bc1/schools/mcas/cs/pdf/honors-thesis/Ward_Brian_Thesis.pdf)
at Boston College.

* [Slexer.mll](Slexer.mll): lexer specification
* [Sparser.vy](Sparser.vy): parser specification, in Coq Menhir
* [error.messages](error.messages): error messages

## Compiler passes

| Pass | Source | Target | Code | Proof |
| ---- | ------ | ------ | ---- | ----- |
| Implement sampling statement | Stanlight | Stanlight | [Sampling](Sampling.v) | [Samplingproof](Samplingproof.v) |
| Reparameterize constrained parameters | Stanlight | Stanlight | [Reparameterization](Reparameterization.v) | [Reparameterizationproof](Reparameterizationproof.v) |
| Optimize out additive constants | Stanlight | Stanlight | [AdditiveConst](AdditiveConst.v) | [AdditiveConstproof](AdditiveConstproof.v) |
| Pull calls out of expressions, compile for loops, translate types to C types, translate operators | Stanlight| CStan | [Clightification](Clightification.v) | [Clightificationproof](Clightificationproof.v) |
| Replace gloval parameters and data by structures | CStan | CStan | [AllocateVariables](AllocateVariables.v) | [AllocateVariablesproof](AllocateVariablesproof.v) |
| Explicit target | CStan | CStan | [Target](Target.v) | [Targetproof](Targetproof.v) |
| Generate Clight | CStan | Clight | [Sbackend](Sbackend.v) | [Sbackendproof](Sbackendproof.v) |

## All together

* [Scompiler](Scompiler.v): defines the overall compilation and proof of semantics preservation

## To learn more

Check out [DEVELOPERS.md](DEVELOPERS.md) for additional information on
some of the files, and tips about extending the compiler and run time.