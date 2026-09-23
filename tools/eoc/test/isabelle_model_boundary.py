#!/usr/bin/env python3
"""Check that model-smt can be added without changing Isabelle's checker.

Example (ethos-eoc must already be built):
  python3 tools/eoc/test/isabelle_model_boundary.py \
    ~/cvc5-ajr/proofs/eo/cpc/Cpc.eo \
    --semantics tools/eoc/semantics/development-cpc.eos

This tests the compilation boundary, not Isabelle model generation (which is
not implemented yet). Both a selected fragment and the full signature pass
through model-smt before the existing checker dependencies are selected again.
Every generated checker, spec, and parser artifact must remain byte-identical.
Like other EOC tests, this writes the build's shared plugin output directory;
do not run it concurrently with another compilation using that build.
"""

import argparse
from pathlib import Path
import re
import sys
import tempfile


EOC = Path(__file__).resolve().parents[1]
ROOT = EOC.parents[1]
sys.path.insert(0, str(EOC))
from driver import ISABELLE_DEPS, Pipeline, compile_signatures


ARTIFACTS = (
    "isabelle_meta_gen.thy", "isabelle_meta_spec_gen.thy", "syntax_gen.json",
    "parser_gen.ML", "sexp_gen.ML", "generate_syntax_gen.py",
)


def check(pipeline, source, directory):
    directory.mkdir()
    desugared = directory / "desugar.eo"
    pipeline.desugar(str(source), desugared, use_vc_plugin=False,
                     deps=ISABELLE_DEPS, plugin_label="isabelle-meta")
    # Match the current checker-only driver: no model dependency echo survives.
    bare = directory / "without-model.eo"
    bare.write_text(re.sub(r'^\(echo "include model_smt[^\n]*\)\n', "",
                           desugared.read_text(), flags=re.M))

    def checker_output(input_file, trimmed_file):
        pipeline.trim_defs(str(input_file), ISABELLE_DEPS.split(), trimmed_file)
        pipeline.ethos(["--plugin.isabelle-meta", str(trimmed_file)], quiet=True)
        return {name: pipeline.plugin_generated(f"isabelle_meta/{name}").read_bytes()
                for name in ARTIFACTS}

    before = checker_output(bare, directory / "checker-before.eo")
    modeled = directory / "with-model.eo"
    pipeline.model_smt(desugared, modeled)
    pipeline.parse_file(modeled)
    after = checker_output(modeled, directory / "checker-after.eo")
    changed = [name for name in ARTIFACTS if before[name] != after[name]]
    if changed:
        raise AssertionError(f"{directory.name}: model-smt changed {', '.join(changed)}")
    print(f"{directory.name}: all {len(ARTIFACTS)} artifacts unchanged")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--semantics", type=Path, required=True)
    parser.add_argument("--smt-semantics", type=Path)
    parser.add_argument("--build-dir", type=Path, default=ROOT / "build-eoc")
    parser.add_argument("--targets", nargs="+", default=["contra"])
    args = parser.parse_args()
    defs, smt, lean, desugar = compile_signatures(
        args.semantics.resolve(),
        args.smt_semantics.resolve() if args.smt_semantics else None)
    with tempfile.TemporaryDirectory(prefix="eoc-isabelle-model-boundary-") as temp:
        output = Path(temp)
        pipeline = Pipeline(args.build_dir, output, 4, None, [],
                            defs, smt, lean, desugar)
        selected = output / "selected.eo"
        pipeline.trim_defs(str(args.input.resolve()), args.targets, selected)
        check(pipeline, selected, output / "selected")
        check(pipeline, args.input.resolve(), output / "all")


if __name__ == "__main__":
    main()
