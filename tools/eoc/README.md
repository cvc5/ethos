# EOC Workflow

`tools/eoc/driver.py` is the canonical entrypoint for the optional
`ethos-eoc` workflow. It replaces the old collection of
`build-debug/run_gen_*` wrapper scripts with one documented interface.

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

## Building `ethos-eoc`

From the repository root:

```bash
./configure.sh debug
cmake --build build --target ethos-eoc -j4
```

If you use a different build directory, pass it explicitly everywhere with
`--build-dir`.

## One important path rule

The driver resolves input paths relative to the directory where you invoke
`python3 tools/eoc/driver.py`, not relative to the build directory.

For example, from the repository root:

```bash
python3 tools/eoc/driver.py vc --build-dir build tests/Booleans-rules.eo and_intro
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
  desugar-pcv.eo
  lean-*-trim.eo
  lean-*-desugar.eo
  lean-*-defs.eo
  lean-*-final.eo
  trim_defs/trim_gen.eo
  vc/final-*.smt2
  sygus/final-*.sy
  pcv/check-*.smt2
  lean/
    Logos.lean
    SmtEval.lean
    SmtModel.lean
    Spec.lean
    Lemmas.lean
```

## Quick start

Generate one VC:

```bash
python3 tools/eoc/driver.py vc --build-dir build tests/Booleans-rules.eo and_intro
```

Generate one SyGuS query:

```bash
python3 tools/eoc/driver.py vc --build-dir build --sygus tests/Booleans-rules.eo and_intro
```

Generate Lean for selected rules:

```bash
python3 tools/eoc/driver.py lean --build-dir build tests/Booleans-rules.eo and_intro contra
```

Generate Lean for the whole signature:

```bash
python3 tools/eoc/driver.py lean --build-dir build --all ../../cvc5-ajr/proofs/eo/cpc/Cpc.eo
```

List all rules declared by a signature and its includes:

```bash
python3 tools/eoc/driver.py list-rules ../../cvc5-ajr/proofs/eo/cpc/Cpc.eo
```

Run every discovered rule through the VC pipeline:

```bash
python3 tools/eoc/driver.py batch --build-dir build vc ../../cvc5-ajr/proofs/eo/cpc/Cpc.eo --all-rules --clean
```

Run every discovered rule through the SyGuS pipeline:

```bash
python3 tools/eoc/driver.py batch --build-dir build sygus ../../cvc5-ajr/proofs/eo/cpc/Cpc.eo --all-rules --clean
```

## Command reference

### `vc`

Generate a single SMT2 VC for one rule.

```bash
python3 tools/eoc/driver.py vc --build-dir build INPUT RULE
```

Useful options:

- `--sygus`: generate a SyGuS query instead of SMT2
- `--skip-cvc5`: skip parse checks with `cvc5`
- `--no-build`: do not rebuild `ethos-eoc` first
- `--cvc5 /path/to/cvc5`: override the solver used for parse checks

### `batch`

Run many rules through the same pipeline.

```bash
python3 tools/eoc/driver.py batch --build-dir build vc INPUT RULE1 RULE2 RULE3
```

Useful options:

- `--all-rules`: discover all `(declare-rule ...)` entries recursively
- `--rules-file FILE`: read one rule name per line from a file
- `--clean`: remove old files from `out/vc` or `out/sygus` first
- `--keep-going`: continue after failures and report all failed rules
- `--skip-cvc5`
- `--no-build`

### `lean`

Generate Lean output either for selected rules or for the full signature.

Selected rules:

```bash
python3 tools/eoc/driver.py lean --build-dir build INPUT RULE1 RULE2
```

Whole signature:

```bash
python3 tools/eoc/driver.py lean --build-dir build --all INPUT
```

Generated files are written to `tools/eoc/out/lean/` by default.

### `desugar`

Generate the desugared EO form of an input.

```bash
python3 tools/eoc/driver.py desugar --build-dir build INPUT
```

Output:

```text
tools/eoc/out/desugar.eo
```

### `pc-valid`

Generate the SMT query used to compare proof-checking behavior.

```bash
python3 tools/eoc/driver.py pc-valid --build-dir build INPUT
```

Output:

```text
tools/eoc/out/pcv/check-<input>.smt2
```

### `trim-defs`

Run only the trim stage.

```bash
python3 tools/eoc/driver.py trim-defs --build-dir build INPUT TARGET1 TARGET2
```

### `list-rules`

Print discovered rules without running the pipeline.

```bash
python3 tools/eoc/driver.py list-rules INPUT
```

This walks `include` chains and preserves declaration order.

## Common workflows

### Reproduce the old `run_gen_vc_single`

```bash
python3 tools/eoc/driver.py vc --build-dir build INPUT RULE
```

### Reproduce the old "run all rules" scripts

```bash
python3 tools/eoc/driver.py batch --build-dir build vc INPUT --all-rules --clean
python3 tools/eoc/driver.py batch --build-dir build sygus INPUT --all-rules --clean
```

### Generate Lean and then copy files elsewhere

```bash
python3 tools/eoc/driver.py lean --build-dir build --all INPUT
ls tools/eoc/out/lean
```

If you previously used `install_logos` or `install_logos_mini`, compatibility
wrappers now live under `tools/eoc/cpc/`. They still run the `lean` pipeline
through `driver.py`, then copy the generated Lean files from `tools/eoc/out/lean`
into your downstream Logos trees using the old default paths unless you
override them with environment variables.

### Manually inspect or debug intermediate files

The driver writes the staged EO files into `tools/eoc/out/`. You can pass those
directly to `ethos-eoc` if you want to debug a later stage manually.

Examples:

```bash
build/src/ethos-eoc tools/eoc/out/trim-d-booleans-rules.eo
build/src/ethos-eoc --plugin.smt-meta tools/eoc/out/vcmt-def-booleans-rules.eo
build/src/ethos-eoc --plugin.smt-meta-sygus tools/eoc/out/vcmt-def-booleans-rules.eo
```

## Migration from the old `build-debug` scripts

| Old script | Replacement |
| --- | --- |
| `run_gen_vc_single INPUT RULE` | `python3 tools/eoc/driver.py vc --build-dir build INPUT RULE` |
| `run_gen_vc_all_* [INPUT]` | `python3 tools/eoc/driver.py batch --build-dir build vc INPUT --all-rules --clean` |
| `run_gen_sygus RULE` | `python3 tools/eoc/driver.py vc --build-dir build --sygus INPUT RULE` |
| `run_gen_sygus_all [INPUT]` | `python3 tools/eoc/driver.py batch --build-dir build sygus INPUT --all-rules --clean` |
| `run_gen_lean INPUT RULE...` | `python3 tools/eoc/driver.py lean --build-dir build INPUT RULE...` |
| `run_gen_lean_all [INPUT]` | `python3 tools/eoc/driver.py lean --build-dir build --all INPUT` |
| `run_gen_desugar_all [INPUT]` | `python3 tools/eoc/driver.py desugar --build-dir build INPUT` |
| `run_gen_pc_valid INPUT` | `python3 tools/eoc/driver.py pc-valid --build-dir build INPUT` |
| `run_trim_defs INPUT TARGET...` | `python3 tools/eoc/driver.py trim-defs --build-dir build INPUT TARGET...` |
| `mkscripts INPUT` | `python3 tools/eoc/driver.py list-rules INPUT` |
| `debug_smt_meta` | Run `build/src/ethos-eoc` directly on files in `tools/eoc/out/` while debugging a late stage |
| `run_test_plugin` | Use `desugar`, `vc`, `pc-valid`, or direct `ethos-eoc` invocations shown above |
| `run_sygus_cex FILE.sy` | Invoke your preferred solver directly on `tools/eoc/out/sygus/final-*.sy` |
| `install_logos` / `install_logos_mini` | `tools/eoc/cpc/install_logos` / `tools/eoc/cpc/install_logos_mini` |

The old wrapper scripts have been removed so the repository only exposes one
supported EOC interface.

## Solver configuration

By default, parse checks use:

1. `--cvc5 /path/to/cvc5`, if passed
2. `$CVC5`, if set
3. `~/bin/cvc5-test`, if it exists

If none of those exist, either pass `--skip-cvc5` or set `CVC5`.

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
published outputs. The plugin-private scratch files remain under
`<build-dir>/out/plugins/`.
```

Plugin-private outputs:

```text
<build-dir>/out/plugins/
  ...
```
