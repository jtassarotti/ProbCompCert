#!/bin/bash

# This script is for development use

# Clean everything
pushd classics/$1/
if [ $? -ne 0 ]; then
    echo 'Test not found. Possible tests are: '
    ls classics
    exit
fi
rm *.o
rm *.s
rm executable
popd

# Compilation
pushd classics/$1/
../../../../ccomp -c stanlib.c
if [ $? -ne 0 ]; then
    echo 'Compilation of stan library failed'
    exit
else
    echo "Compilation success: library"
fi
../../../../ccomp -c parser.c
if [ $? -ne 0 ]; then
    echo 'Compilation of runtime parser failed'
    exit
else
    echo "Compilation success: runtime parser"
fi
../../../../ccomp -c code.light.c
if [ $? -ne 0 ]; then
    echo 'Compilation of stan program' $1 'failed'
    cat code.stan.c.* > code.stan.c.all
    exit
else
    echo 'Compilation success: stan'
fi
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
../../../../ccomp parser.o stanlib.o prelude.o Runtime.o code.light.o -o executable -lm

# Run
./executable $2 data.json params.json
popd



