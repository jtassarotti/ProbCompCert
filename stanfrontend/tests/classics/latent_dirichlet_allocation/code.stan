data {
  int<lower=1, upper=100> w[100];    // word n
  int<lower=1, upper=100> doc[100];  // doc ID for word n
  real<lower=0> alpha;     // topic prior
  real<lower=0> beta;      // word prior
}
parameters {
  simplex[100] theta[100];    // topic dist for doc m
  simplex[100] phi[100];      // word dist for topic k
}
model {
  for (m in 1:100) {
    theta[m] ~ dirichlet(alpha);  // prior
  }
  for (k in 1:100) {
    phi[k] ~ dirichlet(beta);     // prior
  }
  for (n in 1:100) {
    real gamma[100];
    for (k in 1:100) {
      gamma[k] = log(theta[doc[n], k]) + log(phi[k, w[n]]);
    }
    target += log_sum_exp(gamma);  // likelihood;
  }
}