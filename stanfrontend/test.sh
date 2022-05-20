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
rm code.stan.c.*
rm code.stan.c.all
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
else
    echo "Compilation success: library"
fi
../../../../ccomp -c -dcstan -dclight code.stan
if [ $? -ne 0 ]; then
    echo 'Compilation of stan program' $1 'failed'
    cat code.stan.c.* > code.stan.c.all
    exit
else
    echo 'Compilation success: stan'
fi
cat code.stan.c.* > code.stan.c.all
../../../../ccomp -c code.s
../../../../ccomp -I. -c prelude.c
if [ $? -ne 0 ]; then
    echo 'Compilation of prelude failed'
    exit
else
    echo "Compilation success: prelude"
fi
../../../../ccomp -I. -c Runtime.c
if [ $? -ne 0 ]; then
    echo 'Compilation of runtime failed'
    exit
else
    echo "Compilation success: runtime"
fi
../../../../ccomp -lm stanlib.o prelude.o Runtime.o code.o -o executable

# Run
./executable $2 data.csv params.csv
popd



