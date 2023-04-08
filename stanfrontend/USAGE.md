# Running ProbCompCert

This document walks through an example of using ProbCompCert to
(1) compile a Stan program, (2) run the compiled program to generate
samples, and (3) analyze the samples using Stan's analysis
tool, `stansummary`.

At the end of the document, we list some of the limitations/misisng
language features from ProbCompCert relative to official Stan.

*Note*: this file assumes you have a working copy of ProbCompCert
installed. If not, see the INSTALL.md file in this directory

Thoughout this file, we will give paths/tool names using the directory
layout in ProbCompCert's Docker/qemu VM artifact. In those
configurations, the root of the git repository for ProbCompCert is in
the directory /pcc/ProbCompCert

## Getting Started: Coin Flips

We will start with the coin flip example program that is found in
ProbCompCert's benchmark suite. You can find this example in
`ProbCompCert/pcp/stanfrontend/tests/bench/coin_flip`.

The example is relatively short and simple:

```
$ cd stanfrontend/tests/bench/coin_flip
$ cat code.stan
data {
  int flips[100];
}
parameters {
  real<lower=0.0,upper=1.0> mu;
}
model {
  mu ~ uniform(0,1);
  for (i in 1:100) {
    flips[i] ~ bernoulli(mu);
  }
}
```

The data here consists of an array of 100 coin flips, where the
outcome of each flip is represented by an integer. The program has a
single parameter, mu, which represents the probability that the coin
flip returns 1. This parameter is constrained to lie in the interval
[0, 1]. The model block specifies a prior `uniform(0, 1)` distribution
on `mu`, and that each `flip[i]` is sampled according to
`bernoulli(mu)`.

We can compile the program as follows:

```
$ ../../../../ccomp -o coin.exe code.stan
```

(We elide the output of this command.). The `-o coin.exe` specifies
that the compiled executable should be called `coin.exe`.

ProbCompCert also supports producing output for the intermediate
representations generated during compilation. For example, if we do

```
$ ../../../../ccomp -dclight -o coin.exe code.stan
```

A file called "code.light.c" will be produced containing the CompCert
Clight IR generated.

To run the generated binary, we need a data set to analyze, as well as
an initial starting assignment for the parameters (in this case, just
mu).  ProbCompCert generated binaries expect these to be specified in
JSON files, following the format used by cmdstan, the version of Stan
used for generating command-line executables.

The ProbCompCert repository already contains data and parameters for
this initial example, which you can find in `data.json` and
`init.json` in the `bench/coin_flip` directory we're currently in:

```
$ cat data.json
{"flips": [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1,
0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0,
0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]}
$ cat params.json
{"mu": 0.254}
$ grep -o "1" data.json | wc -l
21
```

From the last command, we can see there are 21 flips with value 1, so maximum
likelihood estimate for mu would be 0.21.

We can invoke the the sampler as follows:
```
./coin.exe --num_samples 10 --data data.json --init params.json
```
(output emitted)

The `--data` option specifies the data file, `--init` specifies the
initial parameter value file, and `--num_samples` specifies how many
samples to generate.  So this command will generate 10 samples using
the data/parameters we just saw. The output parameters are put in a
file called `output.csv` in the same directory:

```
$ cat output.csv
lp__,accept_stat__,stepsize__,int_time__,energy__,mu
0.000000,0.000000,0.000000,0.000000,0.000000,0.254000
0.000000,0.000000,0.000000,0.000000,0.000000,0.254000
0.000000,0.000000,0.000000,0.000000,0.000000,0.254000
0.000000,0.000000,0.000000,0.000000,0.000000,0.243173
0.000000,0.000000,0.000000,0.000000,0.000000,0.178682
0.000000,0.000000,0.000000,0.000000,0.000000,0.180567
0.000000,0.000000,0.000000,0.000000,0.000000,0.180567
0.000000,0.000000,0.000000,0.000000,0.000000,0.180567
0.000000,0.000000,0.000000,0.000000,0.000000,0.180567
0.000000,0.000000,0.000000,0.000000,0.000000,0.180567
```

(the last column of this output is randomized and hence will vary
when you run it).

The format of this CSV file matches the ones produced by
`cmdstan`. Each row represents one state of the Markov chain, and
hence correspond to one sample. The first several columns are not
relevant to ProbCompCert, because they involve diagnostic information
that Stan tracks about its particular Markov Chain Monte Carlo
algorithm, hence ProbCompCert generated binaries just emit "0.000000"
for each of these entries. The last column, which is labeled "mu",
contains the values for the mu parameter in the corresponding sample.

If you have Stan installed, you can use the `stansummary` tool to print
some summary statistics about the samples generated:

```
$ stansummary output.csv
Warning: non-fatal error reading metadata
Warning: non-fatal error reading adaptation data
Inference for Stan model:
1 chains: each with iter=(10); warmup=(0); thin=(0); 10 iterations saved.

Warmup took 0.00 seconds
Sampling took 0.00 seconds

                Mean     MCSE  StdDev    5%   50%   95%    N_Eff  N_Eff/s    R_hat

lp__            0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan
accept_stat__   0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan
stepsize__      0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan
int_time__      0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan
energy__        0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan

mu              0.21    0.019   0.037  0.18  0.18  0.25      3.9      inf      1.9

Samples were drawn using  with .
For each parameter, N_Eff is a crude measure of effective sample size,
and R_hat is the potential scale reduction factor on split chains (at
convergence, R_hat=1).
```

Most of the output generated is not relevant here, because it has to
do with Stan's MCMC diagnostics that are not related to ProbCompCert's
form of inference.  However, the row labeled `mu` is meaningful: it
prints the mean, monte carlo standard error (MCSE), standard
deviation, the 5%, 50%, and 95% percentile values, and N_eff an estimate of
the number of "effective samples". From the 5%-95% percentile values
we can form a Bayesian credibility interval for the parameter.

To understand N_eff, the effective samples column, recall that in
Monte Carlo Markov Chain algorithms, such as the one used in
ProbCompCert and Stan, we generate samples by iterating transitions of
a Markov Chain, where the state after each transition is recorded as a
sample. Thus, the samples are not independent, and are often highly
correlated.  For example, in the above output from `cat output.csv`,
you can see that several samples in a row have the same value. This is
because the chain "rejected" making a transition and stayed in the
same state, generating the same sample as the previous state.
A large number of samples that are highly correlated in this way may thus
be less informative than a smaller number of less correlated samples.

The effective sample count is a measure `stanoutput` tries to account
for this and (very roughly) gives in some sense a measure of how many
"distinct" samples there are.  The Stan reference manual contains
[more information](https://mc-stan.org/docs/reference-manual/effective-sample-size.html).

In this case, even though we drew relatively few samples, the mean
estimate was fairly close to the MLE estimate. On the other hand we
also started the chain fairly close to this MLE estimate.

Let's re-run the model, this time starting at a far away point and
collecting far more samples.  The file `params2.json` initializes `mu`
to .8:

```
$ cat params2.json
{"mu": 0.8}
```

This time, we will also use the `--thin`, which lets us only record
every nth sample, instead of saving all of them:

```
./coin.exe --num_samples 1000000 --thin 1000 --data data.json --init params2.json
```
(this takes about 15 seconds to run on the author's machine)

This will run the Markov chain for 1000000 iterations, but only record
everyth 1000th sample that is generated.  Hence, generating only 1000
total samples:

```
$ wc -l output.csv
1001 output.csv
```

Thinning is useful precisely because of the autocorrelation between
successive samples in the Markov chain. By skipping n intermediate
samples, we reduce some of the autocorrelation between samples.

```
$ stansummary output.csv
Warning: non-fatal error reading metadata
Warning: non-fatal error reading adaptation data
Inference for Stan model:
1 chains: each with iter=(1000); warmup=(0); thin=(0); 1000 iterations saved.

Warmup took 0.00 seconds
Sampling took 0.00 seconds

                Mean     MCSE  StdDev    5%   50%   95%    N_Eff  N_Eff/s    R_hat

lp__            0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan
accept_stat__   0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan
stepsize__      0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan
int_time__      0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan
energy__        0.00      nan    0.00  0.00  0.00  0.00      nan      nan      nan

mu              0.22  1.4e-03   0.043  0.15  0.22  0.29      926      inf      1.0

Samples were drawn using  with .
For each parameter, N_Eff is a crude measure of effective sample size,
and R_hat is the potential scale reduction factor on split chains (at
convergence, R_hat=1).
```

As expected, the generated samples again have a mean close to the MLE
of 0.22.

# Not Yet Supported Features

ProbCompCert does not support the full Stan language. Here are some
missing features (not exhaustive): vectors, multi-dimensional arrays,
multi-dimensional constraints, ODE solvers, user defined functions.

Additionally, ProbCompCert's standard library lacks many built-in
distrubtions and math functions that are found in Stan. Here are the
supported distribution/PDF functions in `stanlib.h`:

```
double uniform_lpdf(double x, double a, double b);
double uniform_lpmf(int x, double a, double b);
double normal_lpdf(double x, double mean, double stddev);
double normal_lupdf(double x, double mean, double stddev);
double bernoulli_lpmf(int x, double p);
double cauchy_lpdf(double x, double location, double scale);
double cauchy_lupdf(double x, double location, double scale);
double bernoulli_logit_lpmf(int x, double alpha);
double poisson_lpmf(int x, double lambda);
double exponential_lpdf(double x, double lambda);
```

For the most part, compilation and the correctness proof treat these
distributions as "black boxes", so it is not difficult to extend the
standard library with additional functions. (See DEVELOPERS.md for
information about that).

Additionally, ProbCompCert does not support Stan's "|" syntax for
dividing the arguments of a `_lpdf` function from the distribution's
parameter.  That is, whereas in Stan one may write:

```
normal_lpdf(x | 0, 1)
```

for the log PDF of the Normal(0, 1) distribution at x, in ProbCompCert
one must write:

```
normal_lpdf(x, 0, 1)
```