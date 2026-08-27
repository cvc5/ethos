# CPC Wrappers

These bash scripts are thin CPC-specific front-ends for
`tools/eoc/driver.py`: each fills in the default CPC signature and options,
then invokes the driver.

Most wrappers default to the external CPC signature:

```text
input: <cvc5>/proofs/eo/cpc/Cpc.eo
```

What its symbols mean to the model is said by a signature of its own, which
the wrappers give with `--signature`. What they name there is the central file of
its configuration, `semantics/development-cpc.eos`: the driver compiles that
before the model-smt stage and gives the stage what it compiled to,
`tools/eoc/out/user_defs.eo`, so the two are never out of step. Override it
with `EOC_CPC_SIGNATURE`.

That configuration is also where CPC says what the compilation has no place for
at all,
namely the lambda symbol, its beta-reduction rule, and their private helper
methods; every wrapper leaves those out, not just the ones that compile the
whole signature. The list is literal; no dependency analysis is performed.

`run_gen_vc_all_alethe` defaults to the Alethe signature instead:

```text
<alethe-in-eunoia>/signature/Alethe.eo
```

Useful environment variables:

- `BUILD_DIR=/path/to/build` to override the build tree. If unset, the wrappers
  use the current directory when it contains an executable `ethos-eoc`,
  otherwise `<repo>/build-eoc`.
- `EOC_NO_BUILD=1` to skip the rebuild, for the wrappers that support it,
  namely `run_gen_vc_all`, `run_gen_vc_all_alethe`, `run_gen_sygus_all`,
  `run_gen_lean_all`, `run_trim_defs`, and `run_count_deps`.
- `EOC_SKIP_CVC5=1` to skip solver parse checks.
- `EOC_CPC_INPUT=/path/to/signature.eo` to override the default CPC input. A
  signature given this way has no model definitions unless `EOC_CPC_SIGNATURE`
  names them.
- `EOC_CPC_SIGNATURE=/path/to/defs.eo` to override the signature of the input
  written in the deep embedding.
- `EOC_SEMANTICS=/path/to/smt.eos` to override the SMT-LIB semantics the
  signature of the input is written against, which every input is compiled
  through. Unset, a run leaves the stage the one it ships with; a set named
  here compiles beside itself and is given to the stage with `--semantics`.
- `EOC_CPC_LEAN_CONFIG=/path/to/user_termination.lean` to override the termination
  clauses of the input's programs, which `run_gen_lean` and `run_gen_lean_all`
  give the lean-meta stage with `--lean-config`. A signature given with
  `EOC_CPC_INPUT` gets none unless this names them, on the same terms as
  `EOC_CPC_SIGNATURE`.
- `EOC_ALETHE_INPUT=/path/to/Alethe.eo` to override the default Alethe
  signature.
- `EOC_FINAL_OUT_DIR=/path/to/out` to override the published output tree.
- `LOGOS_DIR`, `LOGOS_TESTS_DIR`, `CVC5_LOGOS`, and `CPC_GEN_LOGOS_CMD` to
  override the `install_logos` destinations and helper command.
- `SUB_DIR` (default `CpcMini`) and `MINI_TARGETS` (default
  `symm contra refl scope trans`) to override the destination package and the
  compiled rule set of `install_logos_mini`.

The install wrappers publish a fixed destination module layout. The generated
Lean module name comes from the input file name up to its first dot, so the
default input `Cpc.eo` generates `Cpc`. If you point
`EOC_CPC_INPUT` at an input that names another calculus, the wrappers detect the
generated module name and rewrite imports back to `Cpc` or `CpcMini` during
installation.

Examples:

```bash
tools/eoc/cpc/run_gen_vc --solve resolution
EOC_CPC_INPUT=tests/Booleans-rules.eo tools/eoc/cpc/run_gen_vc_all --solve
BUILD_DIR=build-eoc EOC_NO_BUILD=1 tools/eoc/cpc/run_gen_lean_all
EOC_CPC_INPUT=tests/Uf-rules.eo EOC_NO_BUILD=1 tools/eoc/cpc/run_count_deps symm
```

`run_gen_vc`, `run_gen_vc_all`, `run_gen_vc_all_alethe`, `run_gen_sygus`, and
`run_gen_sygus_all` accept `--solve` to run the configured `cvc5` executable on
the generated artifact after any parse check. They also accept `--solve-args="..."` to pass
extra solver options through to that solve step, for example
`--solve-args="--tlimit=1000 --seed=7"`.

`run_count_deps RULE [RULE ...]` runs `trim-defs` for each rule and counts the
non-comment, nonblank lines in `tools/eoc/out/trim_defs/trim_gen.eo`, ignoring
`declare-const`, `declare-consts`, and `declare-parameterized-const` commands.
For one rule it prints only the count; for multiple rules it prints
`RULE COUNT` pairs. The counted trimmed EO slice is left at
`tools/eoc/out/trim_defs/trim_gen.eo` for inspection. With multiple rules, this
file contains the slice for the last rule processed.

`install_logos` publishes the generated proof parser as
`$LOGOS_DIR/Cpc/Parser.lean`. The generated module is only a
`Logos.Parser.Config`: the operator and proof-rule tables of the calculus, plus
the mapping of literals, datatype declarations and proof commands into its term
language. The parser itself is the hand-written, calculus-independent
`Logos/Parser.lean` in the Logos repository, which is where that module lives
rather than in a generated calculus package.

`install_logos_mini` passes `--no-parser` to the compiler, skips Parser.lean
when installing the generated modules, and removes any stale
`$LOGOS_DIR/CpcMini/Parser.lean` from an earlier installation.

The tables also cover the identifiers the signature introduces with `define`,
such as `@var` and `@pair`, since proofs use them even though Eunoia inlines
them; see the `lean` section of `tools/eoc/README.md`.

An operator's arity comes from its Eunoia argument-list attribute, carried
through the stages as echo metadata because desugaring strips it from the
emitted declarations. `:arg-list` becomes `.argList`, so `(distinct a b c)`
gathers into `(distinct (@tlist a b c))`; an operator that merely takes a
`@@TypedList` without that attribute, such as `set.insert`, is applied to an
explicit list and stays `.exact`.
