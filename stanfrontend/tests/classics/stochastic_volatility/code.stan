data {
  real y[100];      // mean corrected return at time t
}
parameters {
  real mu;                     // mean log volatility
  real<lower=-1, upper=1> phi; // persistence of volatility
  real<lower=0> sigma;         // white noise shock scale
  real h[100];                 // log volatility at time t
}
model {
  phi ~ uniform(-1, 1);
  sigma ~ cauchy(0, 5);
  mu ~ cauchy(0, 10);
  den = sqrt(1 - phi * phi);
  h[1] ~ normal(mu, sigma / den);
  for (t in 2:100) {
    h[t] ~ normal(mu + phi * (h[t - 1] -  mu), sigma);
  }
  for (t in 1:100) {
    e = exp(h[t] / 2);
    y[t] ~ normal(0, e);
  }
}