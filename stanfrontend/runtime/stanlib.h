#ifndef STANLIB_H_
#define STANLIB_H_

#include <stdio.h>

double randn(double mu, double sigma);

double uniform_sample(double l, double r);
double normal_sample(double mu, double sigma);
double bernoulli_sample(double p);

double logit(double p);
double expit(double a);

double uniform_lpdf(double x, double a, double b);
double uniform_lpmf(int x, double a, double b);
double normal_lpdf(double x, double mean, double stddev);
double normal_lupdf(double x, double mean, double stddev);
double bernoulli_lpmf(int x, double p);
double cauchy_lpdf(double x, double location, double scale);
double cauchy_lupdf(double x, double location, double scale);
double bernoulli_logit_lpmf(int x, double alpha);
double poisson_lpmf(int x, double lambda);
double exponential_lpdf(double x, double lambda); 

void print_int(int i, FILE *fp);
void print_real(double f, FILE *fp);
void print_int_array(int* arr, int N, FILE *fp);
void print_real_array(double* arr, int N, FILE *fp);

#endif // STANLIB_H_
