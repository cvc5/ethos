# EOC Workflow

`tools/eoc/driver.py` is the canonical entrypoint for the optional
`ethos-eoc` workflow.

## What `ethos-eoc` is for

`ethos-eoc` is the optional Eunoia compiler target that drives the
non-standard EOC plugins:

- `desugar`
- `trim-defs`
- `model-smt`
- `smt-meta`
- `lean-meta`

The default `ethos` build does not include these plugins. Use `ethos-eoc`
only when you want the Eunoia-to-SMT2 or Eunoia-to-Lean pipeline.

`model-smt` gives every symbol of the signature its SMT-LIB semantics. A symbol
that instead has no semantics of its own is *eliminated* on the way to the
SMT-LIB term layer, i.e. it is defined in terms of the other symbols of the
signature. Such a reduction is written in the syntax of the signature itself,
as an ordinary `define` whose name is `$eo_reduce_` followed by the symbol it
reduces.

## The signatures written in the deep embedding

What a symbol means to the model is said by two files. The SMT-LIB one is the
target and so is fixed; the one of the input is named with `--defs`:

```text
plugins/model_smt/smt_defs.eo   the SMT-LIB signature, written in the embedding
--defs <file>                   how the input's symbols transform into it,
                                e.g. plugins/model_smt/cpc_defs.eo for CPC
```

```text
python3 tools/eoc/driver.py lean --all \
  --defs plugins/model_smt/cpc_defs.eo <cvc5>/proofs/eo/cpc/Cpc.eo
```

Only the `model-smt` stage reads them; no stage before it sees either. A symbol
the input declares that the file says nothing about is an error rather than a
term the model would silently say nothing about. A run that names no `--defs`
reads `plugins/model_smt/cpc_defs.eo`, which is what the examples below that
compile a signature of CPC symbols rely on.

Each is a sequence of blocks, one per symbol, opened by a `; -- X` line. For a
symbol X, `smt_defs.eo` gives the constructor `$emb_sm.X` and the macro
`$sm_X`, the cases X contributes to `$smtx_typeof` and to `$smtx_model_eval`
(as `$eoc_typeof_X` and `$eoc_eval_X`), and the auxiliary programs those cases
call. `cpc_defs.eo` gives `$eoc_transform_X`, the cases X contributes to
`$eo_to_smt`, and `$eoc_transform_type_X` for a type constructor.

What a block says to the compiler is named `$eoc_`, which is what tells it
apart from what the compiler emits: the case of an `$eoc_` program is spliced
into the aggregate its family names, so the name itself never reaches the
generated file. The exception is `$eoc_is_list_nil_X`, which the desugar stage
calls by name and which is therefore emitted as `$eo_is_list_nil_X`.

A block may also be of a helper rather than of a symbol, in which case the
`; -- X` line names the helper itself, e.g. `; -- $smtx_typeof_bv_op_2` for the
typing of a bit-vector operator whose two arguments must be of one width. Such
a block is taken only when a block that is kept names it, so a signature with
no bit-vectors in it compiles to a model that has never heard of them. A helper
belongs in the signature when only theory operators call it; what remains in
`plugins/model_smt/model_smt.eo` is the type language, the value language and
the terms that file declares itself, together with their methods.

The stage takes the blocks of the symbols the input declares, together with
every block those name, and puts what each says where it belongs; it knows
nothing about any symbol itself. A block is copied as *text*, which is what
keeps the definitions of the embedding it names, e.g. `$vsm_bool`, from being
expanded on the way. See `plugins/model_smt/defs_reader.h`.

Both files are ordered so that a symbol follows the ones its cases name, which
is why neither needs a forward declaration. Adding, changing or removing a
symbol is a change to one block and does not require rebuilding `ethos-eoc`.

A block may name a symbol of the *input* rather than of the embedding, as the
transformation of `@quantifiers_skolemize` names `forall` in the pattern it
matches. Trimming a signature to one proof rule has to keep such a symbol, so
the driver reads those dependencies off the blocks and tells `trim-defs`; see
`Pipeline.defs_depends` in `tools/eoc/driver.py`.

A block may also say that the compilation has no place for its symbol at all:
SMT-LIB gives a proof-level binder no meaning, so `lambda` and everything that
reduces an application of one are left out rather than modelled. A block says
so with directives of the following forms:

```lisp
(echo "eoc-exclude symbol lambda")
(echo "eoc-exclude method $beta_reduce")
(echo "eoc-exclude rule beta-reduce")
```

`Pipeline.defs_excludes` collects them and gives them to the desugar stage,
which is what drops what they name; a rule among them is also left out of
`--all-rules`, since there is nothing to verify about it. The names are matched
literally: the compiler neither checks that a name exists nor computes a
dependency closure, so the block has to name every declaration that goes with
the one it omits.

## Why the generated Lean terminates

Lean has to be told why a recursive definition terminates whenever it cannot
see this for itself, and no measure the compiler could guess would do for the
programs that need one. So the clause is stated as the Lean text it is, and the
`lean-meta` stage appends it to the definition of the program it names:

```text
plugins/lean_meta/termination.lean   the programs of the deep embedding, which
                                     every input is compiled through
--lean-config <file>                 the programs of the input signature, e.g.
                                     plugins/lean_meta/cpc_termination.lean
```

A block runs from a line naming one or more programs, written `-- $name ...`,
to the next comment line, and what lies between is the clause. An input whose
programs all recurse structurally needs no file of its own, so `--lean-config`
is optional; without it the generated Lean simply carries no clause for them,
which Lean will reject if one was needed.

## Building `ethos-eoc`

`ethos-eoc` is built by the standalone CMake project in `plugins/`, which
compiles the ethos core sources together with the plugins. The main ethos
build is unaffected. From the repository root:

```bash
cmake -S plugins -B build-eoc
cmake --build build-eoc --target ethos-eoc -j4
```

Pass `-DCMAKE_BUILD_TYPE=Debug` to the configure step for a debug build with
assertions and tracing. The driver configures the build directory
automatically if it does not exist yet.

`--build-dir` defaults to the current working directory, so pass it explicitly
whenever you invoke the driver from somewhere other than the build tree. The
examples below all use `build-eoc`.

## One important path rule

The driver resolves input paths relative to the directory where you invoke
`python3 tools/eoc/driver.py`, not relative to the build directory.

For example, from the repository root:

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc tests/Booleans-rules.eo and_intro
```

The input path `tests/Booleans-rules.eo` is interpreted relative to the
repository root. The driver writes its EO stage files and final published
outputs under `tools/eoc/out` by default.

## Output layout

The driver uses two output trees:

- `tools/eoc/out/` for stage EO files and final published outputs, unless
  overridden with `--final-out-dir` or `EOC_FINAL_OUT_DIR`
- `<build-dir>/out/plugins/` for plugin-private generated files consumed by the
  driver

Published and stage files:

```text
tools/eoc/out/
  trim-*.eo
  trim-d-*.eo
  vcm-def-*.eo
  vcmt-def-*.eo
  desugar.eo
  lean-*-trim.eo
  lean-*-desugar.eo
  lean-*-defs.eo
  lean-*-final.eo
  trim_defs/trim_gen.eo
  vc/final-*.smt2
  sygus/final-*.sy
  lean/
    Logos.lean
    LogosTerm.lean
    Parser.lean
    SmtEval.lean
    SmtModelDefs.lean
    SmtValueOrder.lean
    SmtModel.lean
    Spec.lean
    RuleLemmas.lean
    Rules/
      <Rule>.lean
```

`out/lean/` is what a run publishes, not a Lean package that builds on its own:
the generated modules import `<Calc>.Proofs.CheckerCore` and
`<Calc>.Proofs.RuleSupport.Support`, which the compiler never writes and which
belong to the package the files are installed into. That package holds the
proof-side modules under `Proofs/`, and the published tree is it with that one
component dropped, uniformly: `RuleLemmas.lean` is installed as
`Proofs/RuleLemmas.lean` and `Rules/<Rule>.lean` as `Proofs/Rules/<Rule>.lean`,
which is what the `import <Calc>.Proofs.Rules.<Rule>` lines that the former
carries name. Every other file is installed at the root of the package, where
its name already is its import.

Plugin-private files:

```text
<build-dir>/out/plugins/
  desugar/
  lean_meta/
  model_smt/
  smt_meta/
  trim_defs/
```

## Quick start

Generate one VC:

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc tests/Booleans-rules.eo and_intro
```

Generate one SyGuS query:

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc --sygus tests/Booleans-rules.eo and_intro
```

Generate Lean for selected rules:

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc tests/Booleans-rules.eo and_intro contra
```

Generate Lean for the whole signature:

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc --all <cvc5>/proofs/eo/cpc/Cpc.eo
```

A declaration the signature of the input leaves out of the compilation is
dropped by this run without anything being said on the command line; see "The
signatures written in the deep embedding" above.

List all rules declared by a signature and its includes:

```bash
python3 tools/eoc/driver.py list-rules <cvc5>/proofs/eo/cpc/Cpc.eo
```

Run every discovered rule through the VC pipeline:

```bash
python3 tools/eoc/driver.py batch --build-dir build-eoc vc <cvc5>/proofs/eo/cpc/Cpc.eo --all-rules --clean
```

Run every discovered rule through the SyGuS pipeline:

```bash
python3 tools/eoc/driver.py batch --build-dir build-eoc sygus <cvc5>/proofs/eo/cpc/Cpc.eo --all-rules --clean
```

## Command reference

### `vc`

Generate a single SMT2 VC for one rule.

```bash
python3 tools/eoc/driver.py vc --build-dir build-eoc INPUT RULE
```

Useful options:

- `--sygus`: generate a SyGuS query instead of SMT2
- `--skip-cvc5`: skip parse checks with `cvc5`
- `--solve`: run `cvc5` on the generated VC or SyGuS file after optional parse checks
- `--solve-args "ARGS"`: shell-style string of extra options passed to `cvc5` during `--solve`
- `--no-build`: do not rebuild `ethos-eoc` first
- `--cvc5 /path/to/cvc5`: override the solver used for parse checks

### `batch`

Run many rules through the same pipeline.

```bash
python3 tools/eoc/driver.py batch --build-dir build-eoc vc INPUT RULE1 RULE2 RULE3
```

Useful options:

- `--all-rules`: discover all `(declare-rule ...)` entries recursively
- `--rules-file FILE`: read one rule name per line from a file
- `--clean`: remove old files from `out/vc` or `out/sygus` first
- `--keep-going`: continue after failures and report all failed rules
- `--skip-cvc5`
- `--solve`
- `--solve-args "ARGS"`
- `--no-build`

### `lean`

Generate Lean output either for selected rules or for the full signature.

Selected rules:

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc INPUT RULE1 RULE2
```

Whole signature:

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc --all INPUT
```

Pass `--no-parser` to omit the signature-specific `Parser.lean` artifact while
still generating the remaining Lean modules and per-rule files. This also
removes a stale `Parser.lean` from the selected final output directory.

Pass `--lean-config FILE` to name the termination clauses of the input's own
programs; see "Why the generated Lean terminates" above.

Generated files are written to `tools/eoc/out/lean/` by default, including
per-rule files in `tools/eoc/out/lean/Rules/`. `Parser.lean` is the minimal
calculus-specific instantiation of the generic Logos proof parser: it contains
only the generated operator/rule tables, indexed-operator constructors, and
surface desugaring configuration.

The operator tables also cover the identifiers the input introduces with
`define`. Eunoia inlines a definition, so it has no counterpart in the compiled
signature, but a proof may still use it. The desugar stage therefore re-emits
each definition it can under the name `$parse_<name>`, which the later stages
reparse and otherwise ignore. By convention a definition whose own name begins
with `$` is a helper of the signature and is not preserved, since a proof never
mentions one. A preserved definition contributes to the parser only, never to a
verification condition or to the generated proof checker. A definition that
takes arguments becomes a macro of the parser, and one that takes none becomes a
nullary operator, or an alias of the operator it names so that it inherits its
indices and argument-list attribute.

### `desugar`

Generate the desugared EO form of an input.

```bash
python3 tools/eoc/driver.py desugar --build-dir build-eoc INPUT
```

Output:

```text
tools/eoc/out/desugar.eo
```

### `trim-defs`

Run only the trim stage.

```bash
python3 tools/eoc/driver.py trim-defs --build-dir build-eoc INPUT TARGET1 TARGET2
```

Output:

```text
tools/eoc/out/trim_defs/trim_gen.eo
```

### `list-rules`

Print discovered rules without running the pipeline.

```bash
python3 tools/eoc/driver.py list-rules INPUT
```

This walks `include` chains and preserves declaration order.

## Common workflows

### Generate Lean and then copy files elsewhere

```bash
python3 tools/eoc/driver.py lean --build-dir build-eoc --all INPUT
ls tools/eoc/out/lean
```

### Manually inspect or debug intermediate files

The driver writes the staged EO files into `tools/eoc/out/`. You can pass those
directly to `ethos-eoc` if you want to debug a later stage manually.

Examples:

```bash
build-eoc/ethos-eoc tools/eoc/out/trim-d-booleans-rules.eo
build-eoc/ethos-eoc --plugin.smt-meta tools/eoc/out/vcmt-def-booleans-rules.eo
build-eoc/ethos-eoc --plugin.smt-meta-sygus tools/eoc/out/vcmt-def-booleans-rules.eo
build-eoc/ethos-eoc tools/eoc/out/lean-booleans-rules-final.eo
build-eoc/ethos-eoc --plugin.lean-meta tools/eoc/out/lean-booleans-rules-final.eo
```

## Solver configuration

By default, parse checks use:

1. `--cvc5 /path/to/cvc5`, if passed
2. `$CVC5`, if set
3. `cvc5` on `PATH`

If none of those resolve, either pass `--skip-cvc5` or set `CVC5`.

## Troubleshooting

### `Couldn't open file: ...`

Check which directory you ran the driver from. Input paths are resolved
relative to the current shell directory, not to `--build-dir`.

### `cvc5 executable not found`

Either:

- pass `--skip-cvc5`
- pass `--cvc5 /path/to/cvc5`
- export `CVC5=/path/to/cvc5`

### I want to inspect the generated artifacts directly

Look in `tools/eoc/out/` for both the staged EO artifacts and the final
published outputs. The plugin-private generated files remain under
`<build-dir>/out/plugins/`.
