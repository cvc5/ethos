# Compiling ALF signatures to C++

For the purposes of optimizing proof checking times, the ALF checker supports compiling user signatures to C++, which can subsequently by compiled as part of the ALF checker.
When invoked with the option `--gen-compile`, the ALF checker will generate C++ code corresponding to type checking, evaluation of terms and matching for programs for all definitions it reads.
After incorporating this code by recompiling the checker, this code can be run via the command line option `--run-compile`.

In detail, the recommended steps for compiling an ALF signature are:
1. Run `ethos --gen-compile <signature>`. This will generate `compiled.out.cpp` in the current directory.
2. Replacing the file `./src/compiled.cpp` with this file and recompile `ethos`.
3. Run `ethos --run-compile <proof>`, where `<proof>` includes `<signature>`.

Running with `--run-compile` leads to performance gains that depend on the signature, but are typically up to 50% faster.

# Appendix

## Command line options of ethos

The ALF command line interface can be invoked by `ethos <option>* <file>` where `<option>` is one of the following:
- `--gen-compile`: output the C++ code for all included signatures from the input file.
- `--run-compile`: use the compiled C++ signatures whenever available.


## Notes to get compiling

- Add Compiler as a friend class of TypeChecker.
- Add Executor as a friend class of State.
