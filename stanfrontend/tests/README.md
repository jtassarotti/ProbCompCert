# Test suites

* [classics](classics): Stan implementation of classic models taken from the Stan user guide
* [standev](standev): Stan programs coming from the Stan development team, mainly used to test the parser

# Tools

* [test.sh](test.sh): Build and execute one of the classic examples. All the C files are copied into the example's direcotry so that they can be modified for debugging.
* [debug.sh](debug.sh): Build and execute one of the classic example, without regenerating the prelude and copying the runtime and Stan library. Used for debugging.
* [test_all.sh]: Execute test.sh on all the classic example, producing a brief report