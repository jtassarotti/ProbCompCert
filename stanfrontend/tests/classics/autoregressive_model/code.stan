data {
  real y[100];
}
parameters {
  real alpha;
  real beta;
  real<lower=0> sigma;
}
model {
  for (n in 2:100) {
    y[n] ~ normal(alpha + beta * y[n - 1], sigma);
  }
}