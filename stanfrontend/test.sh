#!/bin/bash

# This script is for development use

# Clean everything
pushd tests/classics/$1/
if [ $? -ne 0 ]; then
    echo 'Test not found. Possible tests are: '
    ls tests/classics
    exit
fi
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
if [ $? -ne 0 ]; then
    echo 'Compilation of stan library failed'
    exit
fi
../../../../ccomp -c -dclight code.stan
if [ $? -ne 0 ]; then
    echo 'Compilation of stan program' $1 'failed'
    exit
else
    echo 'Compilation of stan program' $1 'succeeded'
fi
../../../../ccomp -c code.s
../../../../ccomp -I. -c prelude.c
if [ $? -ne 0 ]; then
    echo 'Compilation of prelude failed'
    exit
fi
../../../../ccomp -I. -c Runtime.c
if [ $? -ne 0 ]; then
    echo 'Compilation of runtime failed'
    exit
fi
../../../../ccomp -lm stanlib.o prelude.o Runtime.o code.o -o executable

# Run
./executable $2 data.csv
popd



