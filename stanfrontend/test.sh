#!/bin/bash

# Compilation
../ccomp -c stanlib.c
../ccomp -c tests/classics/coin_flip.stan
../ccomp -c coin_flip.s
../ccomp -I. -c tests/classics/coin_flip_prelude.c
../ccomp -I. -c tests/classics/coin_flip_runtime.c
../ccomp -L../out/lib/compcert -lm stanlib.o coin_flip_prelude.o coin_flip.o coin_flip_runtime.o -o coin_flip

# Execution
./coin_flip 100 tests/classics/data.csv
