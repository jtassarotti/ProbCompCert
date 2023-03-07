#!/bin/bash

. ./bench_config.sh
echo "Benching $1 (pcc)"

# This script is for development use

# Clean everything
{
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
cp ../runtime/Runtime.c bench/$1/
cp ../runtime/jsmn.h bench/$1/
cp ../runtime/parser.h bench/$1/
cp ../runtime/parser.c bench/$1/
pushd bench/$1/
../../../../ccomp -c stanlib.c
}  > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo 'Compilation of stan library failed'
    exit
else
    echo "Compilation success: library"
fi
../../../../ccomp -c parser.c > /dev/null
if [ $? -ne 0 ]; then
    echo 'Compilation of runtime parser failed'
    exit
else
    echo "Compilation success: runtime parser"
fi
../../../../ccomp -c -dcstan -dclight code.stan > /dev/null
if [ $? -ne 0 ]; then
    echo 'Compilation of stan program' $1 'failed'
    cat code.stan.c.* > code.stan.c.all
    exit
else
    echo 'Compilation success: stan'
fi
cat code.stan.c.* > code.stan.c.all
../../../../ccomp -c code.s > /dev/null
../../../../ccomp -I. -c prelude.c > /dev/null
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
../../../../ccomp parser.o stanlib.o prelude.o Runtime.o code.o -o executable -lm

# Run
rm pcc_timing_$1.txt
echo "Running trials, times given in seconds..."
for i in {1..5}
do
TIMEFORMAT=%R
(time (./executable --num_samples $NUM_SAMPLES --data data.json --init params.json --thin $THIN > /dev/null)) 2>&1 | tee -a pcc_timing_$1.txt
done
popd > /dev/null



