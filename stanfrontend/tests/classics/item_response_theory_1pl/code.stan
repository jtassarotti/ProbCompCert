data {
  int jj[12];  // student for observation n
  int kk[12];  // question for observation n
  int y[12];   // correctness for observation n
}
parameters {
  real delta;            // mean student ability
  real alpha[4];   // ability of student j - mean ability
  real beta[3];    // difficulty of question k
}
model {
  for (i in 1:4) {
    alpha[i] ~ normal(0,1);   // informative true prior
  }
  for (i in 1:3) {
    beta[i] ~ normal(0,1);          // informative true prior 
  }
  delta ~ normal(0.75, 1);      // informative true prior
  for (n in 1:12) {
    y[n] ~ bernoulli_logit(alpha[jj[n]] - beta[kk[n]] + delta);
  }
}