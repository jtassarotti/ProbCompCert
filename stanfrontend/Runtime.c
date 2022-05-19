#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include "stanlib.h"
#include "prelude.h"

double model(struct Data* d, struct Params *__p__);

int main(int argc, char* argv[]) {
  if (argc == 1) {
    printf("One argument required: number of iterations\n");
    printf("optionally, csv files of data in order of declaration\n");
    exit(1);
  }
  int n = atoi(argv[1]);

  struct Data* observations = alloc_data();
  read_data(observations,argv[2],"r");
  print_data(observations);

  struct Params* state = alloc_params();
  read_params(state,argv[2],"r");
  print_params(state);
  struct Params* candidate = alloc_params();
  
  for (int i = 0; i < n; ++i) {

    printf("\n\n\nIteration: %i\n\n\n", i);
    
    print_params(state);
    double lp_parameters = model(observations,state);
    printf("P = %f\n",exp(lp_parameters));

    printf("\nproposal:\n");
    propose(state,candidate);
    print_params(candidate);
    double lp_candidate = model(observations,candidate);
    printf("P = %f\n",exp(lp_candidate));
    
    double lu = log((double) rand() / RAND_MAX);


    if (lu <= lp_candidate - lp_parameters) {
      printf("\n-> Accepted\n");
      copy_params(state,candidate);
      print_params(state);
    } else {
      printf("\n-> Rejected\n");
    }

  } 

  printf("\n...completed execution!");
  printf("\n\nSummary:\n\t");
  print_params(state);
  printf("\n");
  return 0;
  
}
