#!/bin/bash

./test.sh coin_flip 1 2> /dev/null | grep Compilation
./test.sh linear_regression 1 2> /dev/null | grep Compilation
./test.sh autoregressive_model 1 2> /dev/null | grep Compilation
./test.sh change_point_model 1 2> /dev/null | grep Compilation
./test.sh hierarchical_logistic_regression 1 2> /dev/null | grep Compilation
./test.sh item_response_theory_1pl 1 2> /dev/null | grep Compilation
./test.sh soft_k_means 1 2> /dev/null | grep Compilation
./test.sh stochastic_volatility 1 2> /dev/null | grep Compilation

