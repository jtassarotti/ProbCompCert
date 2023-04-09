# Direct Installation

Here we give direct installation instructions for a Linux x86 machine.
We have tested these instructions on Ubuntu 18.04 and 22.04 but they should
probably work on other Linux systems.

To build the proofs and compiler, you will need Coq and
OCaml installed. We use opam for package management. The following
package version numbers are known to be compatible:

- ocaml.4.11.1
- coq.8.12.2
- coq-coquelicot 3.2.0
- menhir.20220210

You can install these with the following commands:

```
opam switch create ocaml.4.11.1
eval $(opam env --switch=ocaml.4.11.1)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install -y coq.8.12.2 coq-coquelicot.3.2.0
opam install -y menhir.20220210
```

Once installed, cd to the ProbCompCert source directory and run:

```
./configure x86_64-linux
```

Then run

```
make
```

This will check the Coq proofs and then extract a build the compiler.
If everything succeeds, this should produce a binary called ccomp
in the root of the source directory.

If you want to use the compiler, you should then also run (you may need to use sudo permissions)

```
make install
```

Assuming this succeeds without error, the compiler is now built.
