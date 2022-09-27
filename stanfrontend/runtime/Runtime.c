#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <getopt.h>
#include "stanlib.h"
#include "prelude.h"

static int debug = 0;

double model(struct Data* d, struct Params *__p__);

int main(int argc, char* argv[]) {


  static struct option long_options[] = {
    {"debug",         no_argument,       &debug, 1},
    {"num_samples",   required_argument, 0, 'n'},
    {"thin",          required_argument, 0, 't'},
    {"init",          required_argument, 0, 'i'},
    {"data",          required_argument, 0, 'd'},
    {NULL,            0,                 NULL, 0},
  };

  int n = 0;
  int thin = 1;
  char *dataname = NULL;
  char *paramsname = NULL;


  while (1) {
    int option_index = 0;
    int c = getopt_long(argc, argv, "n:t:i:d:",
		    long_options, &option_index);

    // No more arguments; break
    if (c == -1)
      break;

    switch (c)
      {
      case 0:
	break;

      case 'n':
	n = atoi(optarg);
	printf("num_samples = %s (%d)\n", optarg, n);
	break;

      case 't':
	thin = atoi(optarg);
	printf("thin = %s (%d)\n", optarg, thin);
	break;

      case 'd':
	dataname = (char *) malloc(strlen(optarg) + 1 * sizeof(char));
	strcpy(dataname, optarg);
	printf("dataname = %s (%s)\n", optarg, dataname);
	break;

      case 'i':
	paramsname = (char *) malloc(strlen(optarg) + 1 * sizeof(char));
	strcpy(paramsname, optarg);
	printf("paramsname = %s (%s)\n", optarg, paramsname);
	break;
    }

  }

  if (dataname == NULL) {
    printf("No data file specified\n");
    exit(1);
  }

  if (paramsname == NULL) {
    printf("No params file specified\n");
    exit(1);
  }

  /*
  if (argc < 4 || argc > 5) {
    printf("Three arguments required: number of iterations, data file, params file\n");
    printf("One argument optional, debug");
    exit(1);
  }
  */


  /*
  if (argc == 5) {
    debug = true;
  }
  */

  FILE *output = fopen("output.csv","w");
  fprintf(output,"lp__,accept_stat__,stepsize__,int_time__,energy__,");
  print_params_names(output);
  fprintf(output,"\n");

  struct Data* observations = alloc_data();
  read_data(observations,dataname,"r");
  if (debug) {
    print_data(observations,stdout);
  }

  struct Params* state = alloc_params();
  read_params(state,paramsname,"r");
  if (debug) {
    print_params(state,false,stdout);
    printf("\n");
  }
  struct Params* candidate = alloc_params();

  struct Params* statistics = alloc_params();
  copy_params(statistics,state);

  int counter = 0;

  for (int i = 0; i < n; ++i) {

    if (debug) {
      printf("\n\n\nIteration: %i\n\n\n", i);
      print_params(state,false,stdout);
      printf("\n");
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
      print_params(candidate,false,stdout);
      printf("\n");
    }

    double lp_candidate = model(observations,candidate);


    if (debug) {
      printf("P = %lf\n",exp(lp_candidate));
    }

    double u = (double) rand() / RAND_MAX;
    double lu = log(u);

    if(debug) {
      printf("u = %f\n", u);
      printf("lu = %f\n", lu);
      printf("lp_candidate - lp_parameters = %f\n", lp_candidate - lp_parameters);
    }



    if (lu <= lp_candidate - lp_parameters) {
      copy_params(state,candidate);
      counter += 1;
      if (debug) {
	printf("\n-> Accepted\n");
	print_params(state,false,stdout);
	printf("\n");
      }
    } else {
      if (debug) {
	printf("\n-> Rejected\n");
      }
    }

    if (debug) {
      printf("i mod thin == %d\n", i % thin);
    }

    copy_params(statistics,state);
    if (i % thin == 0) {
      if (debug) {
	printf("keeping sample\n");
      }
      fprintf(output,"%lf,%lf,%lf,%lf,%lf,",0.0,0.0,0.0,0.0,0.0);
      print_params(statistics,true,output);
      fprintf(output,"\n");
    }
  }

  printf("\nExecution success\n");
  printf("Acceptance ratio: %lf\n", (float)counter / (float)n);

  fclose(output);

  return 0;

}
