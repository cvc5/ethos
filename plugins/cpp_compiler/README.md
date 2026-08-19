# Compiling Eunoia signatures to C++

This experimental plugin generates C++ that reconstructs parsed Eunoia
signatures. Loading the generated code avoids reparsing those signatures: its
`Executor::initialize()` method rebuilds the declarations and marks the source
files as already included.

The plugin intentionally does **not** generate specialized implementations of
type rules or side conditions. Those continue to use Ethos's ordinary type
checker and program evaluator after the signature has been reconstructed.

## Files

- `compiler.{h,cpp}` records parser callbacks and writes `compiled.out.cpp`.
- `executor.{h,cpp}` provides the runtime plugin that loads generated code.
- `compiled.cpp` is an empty placeholder. Replace it with the generated source
  (or compile that source in its place) when embedding the executor.

The plugins are not linked into the default `ethos` binary. Embedders select a
`Compiler` or `Executor` by passing it to `State::setPlugin()`. The repository's
`plugins-compile-check` CMake target compiles all plugin sources with the current
Ethos headers so API drift is caught by CI.
