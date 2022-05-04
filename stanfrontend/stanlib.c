#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#ifndef M_PI
#define M_PI (3.14159265358979323846)
#endif


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

double logit(double p)
{
  return (p <= 0 || p >= 1) ? INFINITY : log(p) - log(1-p);
}

double expit(double a)
{
  return 1 / (1 + exp(-a));
}

double init_unconstrained()
{
  return uniform_sample(-2, 2);
}

void print_start()
{
  printf("state { ");
}
void print_double(double x)
{
  printf("%f ", x);
}
void print_int(int x)
{
  printf("%i ", x);
}
void print_long(long x)
{
  printf("%ld ", x);
}

void print_array_int(int* arrp, int len)
{
  int *max;
  max = arrp + len;
  printf("array<%i>[", len);
  while (arrp < max) {
    printf("%i, ", *arrp++);
  }
  printf("\b\b]\n");
}
void print_end()
{
  printf("}\n");
}
