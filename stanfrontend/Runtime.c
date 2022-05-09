#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include "stanlib.h"
#include "prelude.h"

// Note that we do not respect the Stan spec because we inline
// the transformed data and transformed parameters blocks

double model(void* p);

int main(int argc, char* argv[]) {
  if (argc == 1) {
    printf("One argument required: number of iterations\n");
    printf("optionally, csv files of data in order of declaration\n");
    exit(1);
  }
  int n = atoi(argv[1]);

  load_from_cli(&observations, argv+2);
  //transformed_data(&observations);
  print_data(&observations);

  init_parameters();
  
  void* pi = get_state();
  printf("initial state    : ");
  print_params(pi);


  for (int i = 0; i < n; ++i) {

    printf("\n\n\nIteration: %i\n\n\n", i);
    
    void* pi = get_state();
    print_params(pi);
    //transformed_parameters(pi);
    double lp_parameters = model(pi);
    printf("P = %f\n",exp(lp_parameters));

    printf("\nproposal:\n");
    void* newpi = propose(pi);
    //transformed_parameters(newpi);
    print_params(newpi);
    double lp_candidate = model(newpi);
    printf("P = %f\n",exp(lp_candidate));
    
    double lu = log((double) rand() / RAND_MAX);


    if (lu <= lp_candidate - lp_parameters) {
      printf("\n-> Accepted\n");
      set_state(newpi);
      print_params(pi);
    } else {
      printf("\n-> Rejected\n");
    }

    //generated_quantities(pi);
  } 

  printf("\n...completed execution!");
  printf("\n\nSummary:\n\t");
  print_params(pi);
  printf("\n");
  return 0;
  
}
