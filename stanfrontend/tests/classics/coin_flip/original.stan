data {
  int N;
  int flips[N];
}
parameters {
  real<lower=0.0,upper=1.0> mu;
} 
model {
  mu ~ uniform(0,1);
  for (i in 1:N) {
    flips[i] ~ bernoulli(mu);
  }
} 