#!/bin/bash

pushd classics/$1/
if [ $? -ne 0 ]; then
    echo 'Test not found. Possible tests are: '
    ls classics
    exit
fi
ls code > /dev/null
if [ $? -ne 0 ]; then
    echo "You must install cmdstan and compile the program"
    echo "To install cmdstan:"
    echo "    https://mc-stan.org/docs/2_30/cmdstan-guide/cmdstan-installation.html#installation-from-github"
    echo "To compile, you need to use cmdstan's makefile"
    exit
fi
rm *.c
rm *.o
rm *.s
rm *.h
rm executable
rm code.stan.c.*
rm code.stan.c.all

./code sample num_samples=$2 num_warmup=0 thin=1 adapt engaged=0 algorithm=hmc engine=static metric=unit_e init=params.json data file=data.json

popd
