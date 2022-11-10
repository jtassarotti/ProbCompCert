data {
  real x[200];
  int y[200];
}
parameters {
  real alpha;
  real beta;
}
model {
  alpha ~ normal(0,.1);
  beta ~ normal(0,.1);
  for (i in 1:200) {
    y[i] ~ bernoulli_logit(alpha + beta * x[i]);
  }
}