# CPC Wrappers

What is here installs the generated Lean of the CPC signature into a Logos
tree: `install_logos` does it for the whole calculus and `install_logos_mini`
for the handful of rules `CpcMini` holds. The rest of the directory is what
those two reach -- `run_gen_lean`, `run_gen_lean_all` and `run_clean`, which
fill in the default CPC signature and options and invoke
`tools/eoc/driver.py`, and `common.sh`, which they share.

Nothing else has a wrapper. A verification condition, a SyGuS query, a trimmed
slice of a signature: call the driver, which documents its own options in
[`../README.md`](../README.md).

The wrappers default to the external CPC signature:

```text
input: <cvc5>/proofs/eo/cpc/Cpc.eo
```

What its symbols mean to the model is said by a signature of its own, which
the wrappers give with `--semantics`. What they name there is the central file of
its configuration, `semantics/development-cpc.eos`: the driver compiles that
before the model-smt stage and gives the stage what it compiled to,
`tools/eoc/out/user_defs.eo`, so the two are never out of step. Override it
with `EOC_SEMANTICS`.

That configuration is also where CPC says what the compilation has no place for
at all,
namely the lambda symbol, its beta-reduction rule, and their private helper
methods; every wrapper leaves those out, not just the ones that compile the
whole signature. The list is literal; no dependency analysis is performed.

Useful environment variables:

- `BUILD_DIR=/path/to/build` to override the build tree. If unset, the wrappers
  use the current directory when it contains an executable `ethos-eoc`,
  otherwise `<repo>/build-eoc`.
- `EOC_NO_BUILD=1` to skip the rebuild, which `run_gen_lean_all` supports and
  so `install_logos` does.
- `EOC_SKIP_CVC5=1` to skip solver parse checks.
- `EOC_CPC_INPUT=/path/to/signature.eo` to override the default CPC input. A
  signature given this way has no model definitions unless `EOC_SEMANTICS`
  names them.
- `EOC_SEMANTICS=/path/to/defs.eos` to override the semantics of the input,
  which say what its symbols mean to the model.
- `EOC_SMT_SEMANTICS=/path/to/smt.eos` to override the SMT-LIB semantics the
  input's semantics are written against, which every input is compiled through.
  Unset, a run compiles the set the tool ships with; a set named here stands in
  for it, compiling to the same `tools/eoc/out/smt_defs.eo` and
  `smt_termination.lean`, so no stage can read one semantics' file while
  another is in use.
- `EOC_CPC_LEAN_CONFIG=/path/to/user_termination.lean` to name the termination
  clauses of the input's programs, which `run_gen_lean` and `run_gen_lean_all`
  then give the lean-meta stage with `--lean-config`. A signature given as a
  configuration set compiles its own clauses, which the driver gives that stage
  of itself, so this is for one given already written out.
- `EOC_LEAN_CALC=Name` to name what the generated Lean calls the calculus,
  which is the package it is installed into; the install wrappers set it
  themselves.
- `EOC_FINAL_OUT_DIR=/path/to/out` to override the published output tree.
- `LOGOS_DIR`, `LOGOS_TESTS_DIR`, `LOGOS_REGRESS_DIR` (default
  `$LOGOS_DIR/test/regress`, where the generated `*.cpc.lean` regressions go),
  `CVC5_LOGOS`, and `CPC_GEN_LOGOS_CMD` to override the `install_logos`
  destinations and helper command.
- `SUB_DIR` (default `CpcMini`) and `MINI_TARGETS` (default
  `symm contra refl scope trans`) to override the destination package and the
  compiled rule set of `install_logos_mini`.

The install wrappers publish a fixed destination module layout, and say which
by generating the Lean under the name of the package it is installed into:
`install_logos` compiles as `Cpc` and `install_logos_mini` as `$SUB_DIR`, so
the imports are right where they are written and nothing rewrites them
afterwards. `EOC_LEAN_CALC` names one for a wrapper called on its own; a run
that names none calls the calculus after its input file, up to the first dot.

Examples:

```bash
BUILD_DIR=build-eoc EOC_NO_BUILD=1 tools/eoc/cpc/install_logos
LOGOS_DIR=/tmp/logos tools/eoc/cpc/install_logos_mini
tools/eoc/cpc/run_gen_lean symm contra
```

`run_gen_vc` and `run_gen_sygus` accept `--solve` to run the configured `cvc5`
executable on the generated artifact after any parse check. They also accept
`--solve-args="..."` to pass extra solver options through to that solve step,
for example `--solve-args="--tlimit=1000 --seed=7"`.

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
