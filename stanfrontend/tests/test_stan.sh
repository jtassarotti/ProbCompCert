#!/bin/bash

if [[ ! -v STANPATH ]]; then
    echo "STANPATH not set. Please set it to the root of the cmdstan-2.30.1 build path"
    exit
fi

pushd classics/$1/
if [ $? -ne 0 ]; then
    echo 'Test not found. Possible tests are: '
    ls classics
    exit
fi

rm -f code

stanc --o=code.hpp code.stan
g++ -std=c++1y -pthread -D_REENTRANT -Wno-sign-compare -Wno-ignored-attributes      -I $STANPATH/stan/lib/stan_math/lib/tbb_2020.3/include    -O3 -I src -I $STANPATH/stan/src -I lib/rapidjson_1.1.0/ -I lib/CLI11-1.9.1/ -I $STANPATH/stan/lib/stan_math/ -I $STANPATH/stan/lib/stan_math/lib/eigen_3.3.9 -I $STANPATH/stan/lib/stan_math/lib/boost_1.78.0 -I $STANPATH/stan/lib/stan_math/lib/sundials_6.1.1/include -I $STANPATH/stan/lib/stan_math/lib/sundials_6.1.1/src/sundials    -DBOOST_DISABLE_ASSERTS          -c -Wno-ignored-attributes   -x c++ -o code.o code.hpp
g++ -std=c++1y -pthread -D_REENTRANT -Wno-sign-compare -Wno-ignored-attributes      -I $STANPATH/stan/lib/stan_math/lib/tbb_2020.3/include    -O3 -I src -I $STANPATH/stan/src -I lib/rapidjson_1.1.0/ -I lib/CLI11-1.9.1/ -I stan/lib/stan_math/ -I $STANPATH/stan/lib/stan_math/lib/eigen_3.3.9 -I $STANPATH/stan/lib/stan_math/lib/boost_1.78.0 -I $STANPATH/stan/lib/stan_math/lib/sundials_6.1.1/include -I $STANPATH/stan/lib/stan_math/lib/sundials_6.1.1/src/sundials    -DBOOST_DISABLE_ASSERTS                -Wl,-L,"$STANPATH/stan/lib/stan_math/lib/tbb" -Wl,-rpath,"$STANPATH/stan/lib/stan_math/lib/tbb"      code.o $STANPATH/src/cmdstan/main.o        -Wl,-L,"$STANPATH/stan/lib/stan_math/lib/tbb" -Wl,-rpath,"$STANPATH/stan/lib/stan_math/lib/tbb"   $STANPATH/stan/lib/stan_math/lib/sundials_6.1.1/lib/libsundials_nvecserial.a $STANPATH/stan/lib/stan_math/lib/sundials_6.1.1/lib/libsundials_cvodes.a $STANPATH/stan/lib/stan_math/lib/sundials_6.1.1/lib/libsundials_idas.a $STANPATH/stan/lib/stan_math/lib/sundials_6.1.1/lib/libsundials_kinsol.a  $STANPATH/stan/lib/stan_math/lib/tbb/libtbb.so.2 -o code
rm -f code.o

# ./code sample num_samples=$2 num_warmup=0 thin=1 adapt engaged=0 algorithm=hmc engine=static metric=unit_e init=params.json data file=data.json
./code sample num_samples=$2 init=params.json data file=data.json

popd
