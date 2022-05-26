#!/bin/bash

echo
echo coin_flip
./test.sh coin_flip 1000 2> /dev/null | grep -E 'Compilation|Execution'
#./test.sh coin_flip 1 2>&1 >/dev/null | grep error
echo
echo linear_regression
./test.sh linear_regression 1000 2> /dev/null | grep -E 'Compilation|Execution'
#./test.sh linear_regression 1 2>&1 >/dev/null | grep error
echo
echo autoregressive_model
./test.sh autoregressive_model 1000 2> /dev/null | grep -E 'Compilation|Execution'
#./test.sh autoregressive_model 1 2>&1 >/dev/null | grep error
echo
echo change_point_model
./test.sh change_point_model 1000 2> /dev/null | grep -E 'Compilation|Execution'
#./test.sh change_point_model 1 2>&1 >/dev/null | grep error
# echo
# ./test.sh hierarchical_logistic_regression 1000 2> /dev/null 
# ./test.sh hierarchical_logistic_regression 1 2>&1 >/dev/null | grep error
echo
echo item_response_theory_1pl
./test.sh item_response_theory_1pl 1000 2> /dev/null | grep -E 'Compilation|Execution'
#./test.sh item_response_theory_1pl 1 2>&1 >/dev/null | grep error
# echo
# ./test.sh soft_k_means 1000 2> /dev/null 
# ./test.sh soft_k_means 1 2>&1 >/dev/null | grep error
echo
echo stochastic_volatility
./test.sh stochastic_volatility 1000 2> /dev/null | grep -E 'Compilation|Execution'
#./test.sh stochastic_volatility 1 2>&1 >/dev/null | grep error
echo

