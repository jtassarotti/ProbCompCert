data {
  real<lower=0> r_e;
  real<lower=0> r_l;
  real D[100];
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
  real lp[100];
  lp = rep_vector(log_unif, 100);
  for (s in 1:100) {
    for (t in 1:100) {
      if (t < s)
        lp[s] = lp[s] + poisson_lpmf(D[t] | e);
      else
        lp[s] = lp[s] + poisson_lpmf(D[t] | l);
    }
  }
}
model {
  e ~ exponential(r_e);
  l ~ exponential(r_l);
  target += log_sum_exp(lp);
}