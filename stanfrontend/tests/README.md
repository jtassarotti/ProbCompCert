# Note

Some of the testing tools use cmdstan, the command-line interface to
the Stan statistical modeling
language. [Instructions](https://mc-stan.org/docs/cmdstan-guide/index.html)
to install and use cmdstan.

# Tools

* [test.sh](test.sh): Build and execute one of the examples. All the C files are copied into the example's direcotry so that they can be modified for debugging. The program writes a file output.csv that can be analyzed using [stansummary](https://mc-stan.org/docs/cmdstan-guide/index.html)
* [debug.sh](debug.sh): Build and execute one of the example, without regenerating the prelude and copying the runtime and Stan library. Used for debugging.
* [test_all.sh](test_all.sh): Execute test.sh on all the example, producing a brief report
* [test_stan.sh](test_stan.sh): Test the official stan implementation. To use this, you must first install [cmdstan](https://mc-stan.org/docs/cmdstan-guide/index.html) and use it to compile the stan program.