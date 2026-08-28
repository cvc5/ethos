# The development branch

This branch is the working line for `ethos-eoc`, the optional Eunoia compiler
workflow. The checker itself is on `main` and is not developed here; what is
developed here is everything that reads a signature and compiles it into
something else -- an SMT-LIB verification condition, or a Lean proof checker --
which is not ready to be part of the checker and may never be part of it.

Work lands here first. What proves durable is proposed to `main` on its own,
as a change to the checker or as a self-contained addition; the rest stays.

## What is on it

- **The plugins**, in [`plugins/`](plugins/): `desugar`, `trim-defs`,
  `model-smt`, `smt-meta`, `lean-meta`, and the `cpp_compiler` experiment. They
  build as a project of their own, so the ethos build is untouched by them.
- **The pipeline**, in [`tools/eoc/`](tools/eoc/): `driver.py`, which runs the
  stages in order, and `sem_compile.py`, which compiles the configuration the
  `model-smt` stage reads. Both are documented in
  [`tools/eoc/README.md`](tools/eoc/README.md).
- **The configuration**, in [`tools/eoc/semantics/`](tools/eoc/semantics/):
  what each symbol of SMT-LIB means to a model, and what each symbol of a
  calculus becomes. This is the part with the most design in it, and its own
  [README](tools/eoc/semantics/README.md) documents the language it is written
  in.
- **A CI job** that builds the plugins with assertions and `-Werror` and runs
  three smoke tests through the pipeline, so that neither rots against `src/`.

## What is scaffolding

Some of what is checked in is here to make one person's day-to-day faster
rather than because the branch needs it. It is written down here so that
trimming it is a decision rather than an oversight.

### The cached artifacts under `tools/eoc/out/`

Fourteen files, about 700 KB: the stage `.eo` files of one CPC run, four of the
generated Lean modules, and one verification condition and one SyGuS file. They
are outputs. Nothing in the repository reads them, and every one of them is
rewritten by the next run of the pipeline, which is what makes them noise in a
diff and a merge conflict in a rebase.

**To trim:** delete them and ignore the whole of `tools/eoc/out/`, which is
already ignored file by file for what the compiler writes. Seeing what a change
did to the generated output is better served by generating into two scratch
directories and comparing them -- `--final-out-dir` takes a path -- than by a
snapshot that is only as current as the last person to commit it.

### The `tools/eoc/cpc/` wrappers

Thirteen shell scripts over `driver.py`, and the library they share. Two of
them do work of their own -- `install_logos` compiles the configuration,
generates the whole Lean package and installs it into a Logos tree, and
`install_logos_mini` does the same for the handful of rules `CpcMini` holds.
The rest name an input and a mode and hand over to the driver.

They also encode one machine's layout as their defaults: the CPC signature at
`../cvc5-ajr/proofs/eo/cpc/Cpc.eo`, the Logos tree at `$HOME/logos`, a solver
at `$HOME/bin/cvc5-logos`. Each is overridable, but the defaults are what makes
them convenient, and they work nowhere else.

**To trim:** keep the two installers and the library, since they do something
the driver does not, and drop the thin wrappers -- what they save over the
driver is one flag. Turn the three developer paths into variables a caller must
set, so that a script that cannot work says so instead of failing deep in a
stage on a path that does not exist.

### `development-cpc.eos`

The configuration of the CPC signature, which will live in the Logos repository
rather than here. It is kept as the one exercise of the input side of the
compiler: without it nothing here compiles a real calculus.

**To trim:** when Logos owns it, have CI read it from there. Keeping a copy is
worse than fetching one, because a copy is stale exactly when it matters.

### `smtlibTests/logos-tests/`

Six `.smt2` inputs that `install_logos` turns into Lean regressions in the
Logos tree. They are fixtures of that repository, kept here because the script
that uses them is here.

**To trim:** move them with the script, or with the configuration above.

## What stays

The plugins, the driver, the semantics compiler, the configuration under
`tools/eoc/semantics/`, and the CI job. That is the branch; the rest is the
scaffolding around it.
