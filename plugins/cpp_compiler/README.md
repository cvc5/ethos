# Compiling Eunoia signatures to C++

This experimental plugin generates C++ that reconstructs the parser state of
one or more Eunoia signatures. A custom Ethos binary links that generated code
and loads it during startup, avoiding reparsing the same signatures when a
proof includes them.

Only auto-parsing is generated. Proof-rule type checking and side-condition
program evaluation still use Ethos's ordinary interpreter. This keeps the
generated surface small and preserves the behavior of the standard checker.

## Prerequisites

The build needs:

- a C++17 compiler;
- CMake;
- a CMake-supported build tool, such as Make or Ninja; and
- GMP development headers and libraries (`libgmp-dev` on Ubuntu or `gmp` via
  Homebrew on macOS).

Run all commands from the repository root unless noted otherwise.

## One-command build

Pass the root signature to the provided script:

```sh
plugins/cpp_compiler/build_custom_ethos.sh path/to/signature.eo
```

The default output directory is `build/cpp_compiler_custom`. The script:

1. builds an `ethos` binary with the `Compiler` plugin;
2. runs it on the signature to write `compiled.out.cpp`;
3. rebuilds `ethos` with the `Executor` plugin and that generated source; and
4. copies the finished binary to `build/cpp_compiler_custom/ethos`.

An output directory and build type may be supplied explicitly:

```sh
plugins/cpp_compiler/build_custom_ethos.sh \
  path/to/signature.eo /tmp/my-ethos debug
```

The build type is `release` by default and may be `release` or `debug`.

Run the resulting checker exactly like the normal checker:

```sh
build/cpp_compiler_custom/ethos path/to/proof.eo
```

The proof should contain its normal `(include "path/to/signature.eo")`
command. `State` normalizes that path, asks the executor whether it already
handled the file, and skips parsing when it refers to a signature embedded in
the generated source. The source signature must still exist so normal include
validation can detect misspelled or missing paths.

To display the canonical signature paths embedded in the binary, run:

```sh
build/cpp_compiler_custom/ethos --show-config
```

Includes nested by the root signature are recorded too. Matching accepts the
same file through relative or absolute paths, but the custom binary remains
tied to the files' locations at generation time. Regenerate it after moving a
signature or after changing any signature contents.

## Manual two-stage build

The script is a convenience wrapper around these commands. First configure and
build generator mode:

```sh
cmake -S plugins/cpp_compiler -B build/cpp-generator \
  -DCMAKE_BUILD_TYPE=Release \
  -DETHOS_CPP_COMPILER_MODE=compiler
cmake --build build/cpp-generator --target ethos --parallel
```

Run the generator from the directory where `compiled.out.cpp` should be
written. Supplying an absolute signature path makes the generated location
unambiguous:

```sh
mkdir -p build/cpp-generated
cd build/cpp-generated
../cpp-generator/bin/ethos /absolute/path/to/signature.eo
cd ../..
```

Then configure and build executor mode with the generated source:

```sh
cmake -S plugins/cpp_compiler -B build/cpp-executor \
  -DCMAKE_BUILD_TYPE=Release \
  -DETHOS_CPP_COMPILER_MODE=executor \
  -DETHOS_CPP_COMPILER_GENERATED_SOURCE="$PWD/build/cpp-generated/compiled.out.cpp"
cmake --build build/cpp-executor --target ethos --parallel
build/cpp-executor/bin/ethos path/to/proof.eo
```

The plugin owns this CMake configuration. The repository's root
`CMakeLists.txt` and `src/CMakeLists.txt` remain unchanged from `main`, and the
ordinary Ethos build does not see either plugin mode.

## Include handling and `markIncluded`

`State::markIncluded()` is still necessary internally to deduplicate includes,
but it is a private implementation detail. Generated code does not call it.
Instead, `Plugin::includeFile()` is a pre-parse callback with a Boolean result:

- `Compiler::includeFile()` returns `false`, so `State` parses the signature
  and the compiler records the parser callbacks.
- Generated `Executor::includeFile()` returns `true` for embedded signature
  paths, telling `State` that initialization already reconstructed them and
  their source should not be parsed.
- Other plugins inherit the default `false`, preserving ordinary parsing.

This leaves ownership of the included-file set in `State`, while making the
executor's skip decision explicit at the plugin boundary.

## Source layout and CI

- `compiler.{h,cpp}` records parser callbacks and writes `compiled.out.cpp`.
- `executor.{h,cpp}` provides the runtime plugin API used by generated code.
- `CMakeLists.txt` provides the standalone generator and executor builds.
- `compiled.cpp` is an empty generated-code placeholder for embedders that
  want one.
- `build_custom_ethos.sh` performs the complete two-stage custom build.

The main build's `plugins-compile-check` deliberately excludes this plugin.
The dedicated CI step invokes `build_custom_ethos.sh`, which generates C++,
compiles it, reconstructs parser state, and verifies that the executor skips
the source include. Run that same end-to-end check locally with:

```sh
plugins/cpp_compiler/build_custom_ethos.sh \
  plugins/cpp_compiler/test/signature.eo /tmp/ethos-cpp-compiler debug
/tmp/ethos-cpp-compiler/ethos \
  plugins/cpp_compiler/test/signature.eo
```
