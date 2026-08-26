# Ethos Checker

## A Flexible and Efficient Proof Checker for SMT Solvers

## Building the Ethos checker

You need CMake (>= version 3.12) and GMP to build the Ethos Checker.

To build a regular build, issue:

```bash
cd /path/to/ethos_checker
./configure.sh
    # use --prefix to specify an install prefix (default: /usr/local)
    # use --name=<PATH> for custom build directory
cd <build_dir>   # default is ./build
make             # use -jN for parallel build with N threads
make install     # to install into the prefix specified above
```

The executable, called `ethos`, will be created in the `<build_dir>/src` folder.

The ethos's build system provides the following pre-defined build profiles:

- *release*: Optimized, assertions and tracing disabled.

- *debug*: Unoptimized, debug symbols, assertions, and tracing enabled.

The default build profile is **release**, which you will get if you just run
`./configure.sh`. To choose a different build profile use:

```bash
./configure.sh <profile>
```

## Using the Ethos checker

```
ethos [script]
```
where `script` is a Eunoia script.  See `tests` and `proofs` for examples.

For further details, see the user manual [here](user_manual.md).

## Running Tests

You can add tests in the `tests` directory.

Run them using `make test` in the build directory.

You can also filter tests using regular expressions for example:

```
ctest -R arith
```
