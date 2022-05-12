data {
  real<lower=0> r_e;
  real<lower=0> r_l;
  real D[100];
}
transformed data {
  real n_log_unif;
  real log_unif;
  n_log_unif = log(100);
  log_unif = -n_log_unif;
}
parameters {
  real<lower=0> e;
  real<lower=0> l;
}
transformed parameters {
  real lp[100];
  real pois;
  for (i in 1:100) {
    lp[i] = log_unif;
  }
  for (s in 1:100) {
    for (t in 1:100) {
      if (t < s) {
        pois = poisson_lpmf(D[t],e);
        lp[s] = lp[s] + pois;
      }
      else {
        pois =  poisson_lpmf(D[t], l);
        lp[s] = lp[s] + pois;
      }
    }
  }
}
model {
  real lsp;
  e ~ exponential(r_e);
  l ~ exponential(r_l);
  lsp = log_sum_exp(lp);
  target += lsp;
}