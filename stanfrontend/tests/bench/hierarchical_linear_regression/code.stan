data {
  real x[200];
  real y[200];
  int class[200];
}
parameters {
  real mu;
  real gamma;
  real alpha[2];
  real beta[2];
  real <lower=0.1>sigma;
}
model {
  mu ~ normal(0, 3);
  gamma ~ normal(0, 3);
  sigma ~ normal(1,.1);
  for (i in 1:2) {
    alpha[i] ~ normal(mu, 1);
    beta[i] ~ normal(gamma, 1);
  }
  for (i in 1:200) {
    y[i] ~ normal(alpha[class[i]] + beta[class[i]] * x[i], sigma);
  }
}