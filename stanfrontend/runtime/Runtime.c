#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include <stdbool.h>
#include "stanlib.h"
#include "prelude.h"

double model(struct Data* d, struct Params *__p__);

int main(int argc, char* argv[]) {
  if (argc < 4 || argc > 5) {
    printf("Three arguments required: number of iterations, data file, params file\n");
    printf("One argument optional, debug");
    exit(1);
  }
  bool debug = false;
  if (argc == 5) {
    debug = true;
  }
  
  int n = atoi(argv[1]);

  struct Data* observations = alloc_data();
  read_data(observations,argv[2],"r");
  if (debug) {
    print_data(observations);
  }
    
  struct Params* state = alloc_params();
  read_params(state,argv[3],"r");
  if (debug) {
    print_params(state,false);
  }
  struct Params* candidate = alloc_params();

  int counter = 0;

  for (int i = 0; i < n; ++i) {

    if (debug) {
      printf("\n\n\nIteration: %i\n\n\n", i);
      print_params(state,false);
    }
    
    double lp_parameters = model(observations,state);

    if (debug) {
      printf("P = %lf\n",exp(lp_parameters));
    }

    if (debug) {
      printf("\nproposal:\n");
    }
    
    propose(state,candidate);

    if (debug) {
      print_params(candidate,false);
    }
    
    double lp_candidate = model(observations,candidate);

    if (debug) {
      printf("P = %lf\n",exp(lp_candidate));
    }
      
    double lu = log((double) rand() / RAND_MAX);


    if (lu <= lp_candidate - lp_parameters) {
      copy_params(state,candidate);
      counter += 1;
      if (debug) {
	printf("\n-> Accepted\n");
	print_params(state,false);
      }
    } else {
      if (debug) {
	printf("\n-> Rejected\n");
      }
    }

  } 

  printf("\nExecution success\n");
  print_params(state,true);
  printf("\n");
  printf("Acceptance ratio: %lf\n", (float)counter / (float)n);
  return 0;
  
}
