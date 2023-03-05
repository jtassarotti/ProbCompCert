#!/bin/bash

if [[ ! -v STANPATH ]]; then
    echo "STANPATH not set. Please set it to the root of the cmdstan-2.30.1 build path"
    exit
fi

if [[ ! -v BRIDGEPATH ]]; then
    echo "BRIDGEPATH not set. Please set it to the root of the bridgestan build path"
    exit
fi

# This script is for development use

# Clean everything
cp BridgeMakefile bench/$1/Makefile

pushd bench/$1/
if [ $? -ne 0 ]; then
    echo 'Test not found. Possible tests are: '
    ls bench
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
cp ../runtime/stanlib.h bench/$1/
cp ../runtime/stanlib.c bench/$1/
cp ../runtime/Bridgeruntime.c bench/$1/
cp ../runtime/jsmn.h bench/$1/
cp ../runtime/parser.h bench/$1/
cp ../runtime/parser.c bench/$1/
pushd bench/$1/
gcc -O1 -c stanlib.c -o bridgestanlib.o
if [ $? -ne 0 ]; then
    echo 'Compilation of stan library failed'
    exit
else
    echo "Compilation success: library"
fi
gcc -O1 -c parser.c -o bridgeparser.o
if [ $? -ne 0 ]; then
    echo 'Compilation of runtime parser failed'
    exit
else
    echo "Compilation success: runtime parser"
fi
../../../../ccomp -c -dcstan -dclight code.stan
if [ $? -ne 0 ]; then
    echo 'Compilation of stan program' $1 'failed'
    cat code.stan.c.* > code.stan.c.all
    exit
else
    echo 'Compilation success: stan'
fi
gcc -O1 -I. -c bridgeprelude.c -o bridgeprelude.o
if [ $? -ne 0 ]; then
    echo 'Compilation of prelude failed'
    exit
else
    echo "Compilation success: prelude"
fi
gcc -O1 -c -I $BRIDGEPATH/src -I. Bridgeruntime.c -o Bridgeruntime.o
if [ $? -ne 0 ]; then
    echo 'Compilation of runtime failed'
    exit
else
    echo "Compilation success: runtime"
fi

stanc --o=code.hpp code.stan

CMDSTAN=$STANPATH make Runtime

# Run
./bridge --num_samples $2 --data data.json --init params.json --thin $3
popd



