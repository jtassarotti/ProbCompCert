#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include <stanlib.h>

struct Data;
struct Data {
  int flips[100];
};
struct Data observation;

void* state;
void print_state(void*);

void* get_state();
void set_state(void*);

void data();
void transformed_data();
void parameters();
void transformed_parameters(void* p);
double model(void* p);
void generated_quantities();

void* propose();

void init_data() {
  int num_elements = sizeof(observation.flips) / sizeof(int);
  int mod = 2;
  printf("num_items: %d\n", num_elements);
  for (int i = 0; i <= num_elements; ++i) {
    *( observation.flips+i ) = (i % mod == 0) ? 1 : 0;
  }
  printf("%% 1s: %f\n", (double) ceil((double) num_elements / (double) mod) / 100);
}
void print_data() {
  int num_elements = sizeof(observation.flips) / sizeof(int);
  printf("flips: [");
  for (int i = 0; i < num_elements; ++i) {
    printf("%i, ", *(observation.flips+i));
  }
  printf("\b\b]\n");
}

int main(int argc, char* argv[]) {
  if (argc != 2) {
    printf("One argument required: number of iterations\n");
    exit(1);
  }

  int n = atoi(argv[1]);
  data();
  transformed_data();
  print_data();

  init_data();
  print_data();

  parameters();

  print_state(&state);
  for (int i = 0; i < n; ++i) {

    void* pi = get_state();

    transformed_parameters(pi);
    double lp_parameters = model(pi);

    void* newpi = propose();

    struct Params* ca = (struct Params*) newpi;

    transformed_parameters(newpi);
    double lp_candidate = model(newpi);

    double u = ((double) rand() / RAND_MAX);

    if (u <= lp_candidate - lp_parameters) {
      set_state(newpi);
      printf("setting state in iteration %d: ", i+1); // 1-index iterations
      print_state(&state);
    }

    generated_quantities();
  }

  printf("\t...completed execution!\n\nSummary:\n\t");
  print_state(&state);
  return 0;
  
}
