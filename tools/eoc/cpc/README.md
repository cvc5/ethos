# CPC Compatibility Wrappers

These bash scripts preserve the old `build-debug/run_gen_*` workflow on top of
`tools/eoc/driver.py`.

Most wrappers default to the external CPC signature:

```text
../cvc5-ajr/proofs/eo/cpc/Cpc.eo
```

`run_gen_vc_all_alethe` keeps the old Alethe default:

```text
../AletheInEunoia/signature/Alethe.eo
```

Useful environment variables:

- `BUILD_DIR=/path/to/build` to override the build tree. If unset, the wrappers
  use the current directory when it looks like a build tree, otherwise
  `<repo>/build`.
- `EOC_NO_BUILD=1` for wrappers that previously supported skipping the rebuild.
- `EOC_SKIP_CVC5=1` to skip solver parse checks.
- `EOC_CPC_INPUT=/path/to/Cpc.eo` to override the default CPC signature.
- `EOC_ALETHE_INPUT=/path/to/Alethe.eo` to override the default Alethe
  signature.
- `EOC_FINAL_OUT_DIR=/path/to/out` to override the published output tree.
- `LOGOS_DIR`, `TEST_DIR`, `LOGOS_TESTS_DIR`, `CVC5_LOGOS`, and
  `CPC_GEN_LOGOS_CMD` to override the legacy `install_logos` destinations and
  helper command.

The install wrappers keep their legacy destination module layout. If you point
`EOC_CPC_INPUT` at a non-`Cpc.eo` signature, they detect the generated Lean
module name and rewrite imports back to `Cpc` or `CpcMini` during installation.

Examples:

```bash
tools/eoc/cpc/run_gen_vc --solve resolution
EOC_CPC_INPUT=tests/Booleans-rules.eo tools/eoc/cpc/run_gen_vc_all --solve
BUILD_DIR=build EOC_NO_BUILD=1 tools/eoc/cpc/run_gen_lean_all
```

`run_gen_vc`, `run_gen_vc_all`, `run_gen_sygus`, and `run_gen_sygus_all`
accept `--solve` to run the configured `cvc5` executable on the generated
artifact after any parse check. They also accept `--solve-args="..."` to pass
extra solver options through to that solve step, for example
`--solve-args="--tlimit=1000 --seed=7"`.

Compatibility scripts restored from the old workflow:

- `install_logos`
- `install_logos_mini`
