data {
  real y[10];
}
parameters {
  real alpha;
  real beta;
  real<lower=0> sigma;
}
model {
  for (n in 2:10) {
    y[n] ~ normal(alpha + beta * y[n - 1], sigma);
  }
}