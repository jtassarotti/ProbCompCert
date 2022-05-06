data {
  real<lower=0> r_e;
  real<lower=0> r_l;

  int<lower=1> 100;
  array[100] int<lower=0> D;
}
transformed data {
  real log_unif;
  log_unif = -log(100);
}
parameters {
  real<lower=0> e;
  real<lower=0> l;
}
transformed parameters {
  vector[100] lp;
  lp = rep_vector(log_unif, 100);
  for (s in 1:100) {
    for (t in 1:100) {
      lp[s] = lp[s] + poisson_lpmf(D[t] | t < s ? e : l);
    }
  }
}
model {
  e ~ exponential(r_e);
  l ~ exponential(r_l);
  target += log_sum_exp(lp);
}