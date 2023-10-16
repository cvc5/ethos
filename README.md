# AletheLF Checker

## A Flexible and Efficient Proof Checker for SMT Solvers

## Building the AletheLF checker

You need cmake (>= version 3.12) and gmp to build the AletheLF Checker.

To build a regular build, issue:

```bash
cd /path/to/alethelf_checker
mkdir build
cd build
cmake ..
make
```

The executable, called `alfc`, will be created in the build/src folder.

Alternatively you can configure a regular build with

```bash
cmake -DCMAKE_BUILD_TYPE=Release ..
```
To build a regular build and install it into /path/to/install, issue:

```bash
cd /path/to/alethelf_checker
mkdir build
cd build
cmake -DCMAKE_INSTALL_PREFIX:PATH=/path/to/install ..
make install
```

To build a debug build, issue:

```bash
cd /path/to/alethelf_checker
mkdir build
cd build
cmake -DCMAKE_BUILD_TYPE=Debug ..
make
```

## Using the AletheLF checker

```
alfc [script]
```
where `script` is an AletheLF script.  See `tests` and `proofs` for examples.

For further details, see the user manual [here](user_manual.md).

## Running Tests

You can add tests in the `tests` directory.

Run them using `make test` in the build directory.

You can also filter tests using regular expressions for example:

```
ctest -R arith
```
