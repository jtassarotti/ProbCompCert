data {
  int jj[225];  // student for observation n
  int kk[225];  // question for observation n
  int y[225];   // correctness for observation n
}
parameters {
  real alpha[15];   // ability of student j - mean ability
  real beta[15];    // difficulty of question k
}
model {
  for (i in 1:15) {
    alpha[i] ~ normal(0,10);   // informative true prior
  }
  for (i in 1:15) {
    beta[i] ~ normal(0,10);          // informative true prior 
  }
  for (n in 1:225) {
    y[n] ~ bernoulli_logit(alpha[jj[n]] - beta[kk[n]]);
  }
}
