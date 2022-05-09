#!/bin/bash

# This script is for development use

# Clean everything
pushd tests/classics/$1/
rm *.c
rm *.o
rm *.s
rm *.h
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
../../../../ccomp -I. -c prelude.c
../../../../ccomp -I. -c Runtime.c
../../../../ccomp -lm stanlib.o prelude.o Runtime.o code.o -o executable

# Run
./executable $2 data.csv
popd



