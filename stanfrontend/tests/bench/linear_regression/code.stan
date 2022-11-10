data {
  real x[200];
  real y[200];
}
parameters {
  real alpha;
  real beta;
  real<lower=0.1> sigma;
}
model {
  alpha ~ normal(0,1);
  beta ~ normal(0,1);
  sigma ~ normal(1,.1);
  for (i in 1:200) {
    y[i] ~ normal(alpha + beta * x[i], sigma);
  }
}