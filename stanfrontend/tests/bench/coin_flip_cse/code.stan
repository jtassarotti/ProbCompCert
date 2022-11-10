data {
  int flips[100];
}
parameters {
  real<lower=0.0,upper=1.0> mu;
} 
model {
  real mu2 = mu;
  mu2 ~ uniform(0,1);
  for (i in 1:100) {
    flips[i] ~ bernoulli(mu2);
  }
} 
