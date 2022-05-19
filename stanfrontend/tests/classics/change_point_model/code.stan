data {
  real<lower=0> r_e;
  real<lower=0> r_l;
  int D[10];
}
transformed data {
  real log_unif;
  log_unif = -log(10);
}
parameters {
  real<lower=0> e;
  real<lower=0> l;
}
transformed parameters {
  real lp[10];
  for (i in 1:10) {
    lp[i] = log_unif;
  }
  for (s in 1:10) {
    for (t in 1:10) {
      if (t < s) {
        lp[s] = lp[s] + poisson_lpmf(D[t],e);
      }
      else {
        lp[s] = lp[s] + poisson_lpmf(D[t], l);
      }
    }
  }
}
model {
  e ~ exponential(r_e);
  l ~ exponential(r_l);
  real acc;
  acc = 0;
  for (i in 1:10) {
    acc = acc + exp(lp[i]);
  }
  target += log(acc); 
}