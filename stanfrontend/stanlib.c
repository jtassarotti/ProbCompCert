#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#ifndef M_PI
#define M_PI (3.14159265358979323846)
#endif

/* A random number generator */

double randn (double mu, double sigma)
{
  double U1, U2, W, mult;
  static double X1, X2;
  static int call = 0;

  if (call == 1)
    {
      call = !call;
      return (mu + sigma * (double) X2);
    }

  do
    {
      U1 = -1 + ((double) rand () / RAND_MAX) * 2;
      U2 = -1 + ((double) rand () / RAND_MAX) * 2;
      W = pow (U1, 2) + pow (U2, 2);
    }
  while (W >= 1 || W == 0);

  mult = sqrt ((-2 * log (W)) / W);
  X1 = U1 * mult;
  X2 = U2 * mult;

  call = !call;
 
  return (mu + sigma * (double) X1);
}

/* Samplers: useful for the proposal */

double uniform_sample(double l, double r)
{
  if (l > r) {
    return NAN;
  } else {
	  return l + (rand() / (RAND_MAX / (r - l)));
  }
}

double normal_sample(double mu, double sigma)
{
  return randn(mu, sigma);
}

double bernoulli_sample(double p)
{
  return (((double) rand () / RAND_MAX) > p) ? 0 : 1;
}

/* Ueful math functions */

double logit(double p) {
  return (p <= 0 || p >= 1) ? INFINITY : log(p) - log(1-p);
}

double expit(double a) {
  return 1 / (1 + exp(-a));
}

/* Density and mass functions */

double uniform_lpdf(double x, double a, double b)
{
    /* printf("uniform_lpdf(%f, %f, %f)\n", x, a, b); */
    return (x < a || x > b) ? INFINITY : (-log(b - a));
}

double uniform_lpmf(int x, double a, double b)
{
    double k = (double) x;
    return (k < a || k > b) ? INFINITY : (-log(b - a));
}

double normal_lpdf(double x, double mean, double variance)
{
  return 1 / (sqrt(variance * 2 * M_PI)) * exp(- pow((x-mean),2) / (2 * variance)); 
}

double bernoulli_lpmf(int x, double p)
{
    /* printf("bernoulli_lpmf(%d, %f)\n", x, p); */
    double k = (double) x;
    return k * log(p) + (1-k) * log(1-p);
}

double cauchy_lpdf(double x, double location, double scale)
{
  return 1 / (M_PI * scale * (1 + pow((x - location)/scale,2)));
}

double bernoulli_logit_lpmf(int x, double alpha)
{
  x = (double) x;
  return x * log(expit(alpha)) + (1-x) * log(1 - expit(alpha));
}

double poisson_lpmf(int x, double lambda){
  x = (double) x;
  return 0.0;
}

double exponential_lpdf(double x, double lambda){
  return 0.0;
}

/* Utilities for the data and parameter structures */

void read_int(FILE *fp, int* i) {

  fscanf(fp, "%i", i);

}

void print_int(int i){

  printf("%i\n",i);
  
}

void read_real(FILE *fp,float* f) {

  fscanf(fp, "%f", f);

}

void print_real(float f){

  printf("%f\n",f);
  
}

void read_int_array(FILE *fp, int* arr, int N) {

  for (int i = 0; i < N; i++) {

    read_int(fp,arr + i);
    
  }
  
}

void print_int_array(int* arr, int N) {

  for (int i = 0; i < N; ++i) {
    printf("%i ", arr[i]);
  }
  printf("\n");

}

void read_real_array(FILE *fp, float* arr, int N) {

  for (int i = 0; i < N; i++) {

    read_real(fp,arr + i);
    
  }
  
}

void print_real_array(float* arr, int N) {

  for (int i = 0; i < N; ++i) {
    printf("%f ", arr[i]);
  }
  printf("\n");

}
