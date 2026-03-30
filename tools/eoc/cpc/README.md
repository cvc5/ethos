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

Examples:

```bash
tools/eoc/cpc/run_gen_vc_single tests/Booleans-rules.eo and_intro
EOC_CPC_INPUT=tests/Booleans-rules.eo tools/eoc/cpc/run_gen_vc_all_cpc
BUILD_DIR=build EOC_NO_BUILD=1 tools/eoc/cpc/run_gen_lean_all
```
