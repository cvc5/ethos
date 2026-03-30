`tools/eoc/driver.py` is the canonical entrypoint for the optional `ethos-eoc` workflow.

Examples:

```bash
python3 tools/eoc/driver.py vc --build-dir build tests/Booleans-rules.eo and_intro
python3 tools/eoc/driver.py lean --build-dir build tests/Booleans-rules.eo and_intro
python3 tools/eoc/driver.py batch --build-dir build vc ../../cvc5-ajr/proofs/eo/cpc/Cpc.eo --all-rules --clean
python3 tools/eoc/driver.py list-rules ../../cvc5-ajr/proofs/eo/cpc/Cpc.eo
```

The shell scripts in `build-debug/` remain as compatibility wrappers for existing workflows, but the source-of-truth logic now lives here instead of in ad hoc build-directory scripts.
