# Ethos Checker

## A Flexible and Efficient Proof Checker for SMT Solvers

Ethos checks proofs against proof calculi written in Eunoia. It checks that
each step follows the supplied rules; it does not prove that those rules are
sound. Use `--require-proof-of-false` when a successful run must end in a
refutation. The [user manual](user_manual.md#responses) explains the verdicts
and their limits.

## Building the Ethos checker

You need a C++17 compiler, CMake (>= version 3.12), a build tool such as Make,
and GMP development headers and libraries to build the Ethos Checker.

To build a regular build, issue:

```bash
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
where `script` is a Eunoia script. See [tests/](tests/) for examples.

For further details, see the [user manual](user_manual.md) and the
[documentation index](docs/README.md).

## Running Tests

You can add tests in the `tests` directory.

Run them using `make test` in the build directory.

You can also filter tests using regular expressions for example:

```
ctest -R arith
```

## The name

*Ethos* (ἦθος) is Greek for character or custom. In the context of this tool,
this name refers to the discipline of checking that a proof follows the rules
of its declared calculus.

## How this repository is maintained

Ethos is an **associate** of the Eunoia ecosystem.

- The core of Ethos, the checker in `src/`, is maintained by human
developers, and its code is fully understood by humans.

- The `plugins/` and `tools/` directories are experimental and come with no
guarantees. They are not part of the checker and are not held to the standard
above.

- A pull request is recommended to document whether it was AI assisted.
