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
double normal_lpdf(double x, double mean, double variance);
double bernoulli_lpmf(int x, double p);
double cauchy_lpdf(double x, double location, double scale);
double bernoulli_logit_lpmf(int x, double alpha);
double poisson_lpmf(int x, double lambda);
double exponential_lpdf(double x, double lambda); 

void read_int(FILE *fp, int* i);
void print_int(int i);
void read_real(FILE *fp,double* f);
void print_real(double f);
void read_int_array(FILE *fp, int* arr, int N);
void print_int_array(int* arr, int N);
void read_real_array(FILE *fp, double* arr, int N);
void print_real_array(double* arr, int N);

#endif // STANLIB_H_
