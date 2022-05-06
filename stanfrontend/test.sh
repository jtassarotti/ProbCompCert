#!/bin/bash

# This script is for development use

# Clean everything
pushd tests/classics/$1/
rm *.c
rm *.o
rm *.s
rm executable
popd

# Compilation
cp stanlib.h tests/classics/$1/
cp stanlib.c tests/classics/$1/
cp Runtime.c tests/classics/$1/
pushd tests/classics/$1/
../../../../ccomp -c stanlib.c
../../../../ccomp -c -dclight code.stan
../../../../ccomp -c code.s
../../../../ccomp -I. -c code_prelude.c
../../../../ccomp -I. -c code_runtime.c
../../../../ccomp -lm stanlib.o code_prelude.o code_runtime.o code.o -o executable

# Run
./executable $2 data.csv
popd



