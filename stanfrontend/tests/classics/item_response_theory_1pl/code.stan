data {
  int<lower=1, upper=10> jj[100];  // student for observation n
  int<lower=1, upper=20> kk[100];  // question for observation n
  int<lower=0, upper=1> y[100];   // correctness for observation n
}
parameters {
  real delta;            // mean student ability
  real alpha[10];   // ability of student j - mean ability
  real beta[20];    // difficulty of question k
}
model {
  alpha ~ normal(0,1);         // informative true prior
  beta ~ normal(0,1);          // informative true prior
  delta ~ normal(0.75, 1);      // informative true prior
  for (n in 1:100) {
    y[n] ~ bernoulli_logit(alpha[jj[n]] - beta[kk[n]] + delta);
  }
}