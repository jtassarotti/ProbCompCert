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
fi
../../../../ccomp -c code.light.c
if [ $? -ne 0 ]; then
    echo 'Compilation of stan program' $1 'failed'
    exit
else
    echo 'Compilation of stan program' $1 'succeeded'
fi
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
../../../../ccomp -lm stanlib.o prelude.o Runtime.o code.light.o -o executable

# Run
./executable $2 data.csv params.csv
popd



