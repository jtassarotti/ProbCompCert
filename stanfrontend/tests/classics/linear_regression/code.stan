data {
  real x[100];
  real y[100];
}
parameters {
  real alpha;
  real beta;
  real<lower=0> sigma;
}
model {
  alpha ~ normal(0,1);
  beta ~ normal(0,1);
  sigma ~ normal(0,1);
  for (i in 1:100) {
    y[i] ~ normal(alpha + beta * x[i], sigma);
  }
}