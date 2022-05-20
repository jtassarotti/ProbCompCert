data {
  real y[10];      // mean corrected return at time t
}
parameters {
  real mu;                     // mean log volatility
  real<lower=-1, upper=1> phi; // persistence of volatility
  real<lower=0> sigma;         // white noise shock scale
  real h[10];                 // log volatility at time t
}
model {
  phi ~ uniform(-1, 1);
  sigma ~ cauchy(0, 5);
  mu ~ cauchy(0, 10);
  h[1] ~ normal(mu, sigma / sqrt(1.0 - phi * phi));
  for (t in 2:10) {
    h[t] ~ normal(mu + phi * (h[t - 1] -  mu), sigma);
  }
  for (t in 1:10) {
    y[t] ~ normal(0, exp(h[t] / 2.0));
  }
}