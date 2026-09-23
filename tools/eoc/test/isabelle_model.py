#!/usr/bin/env python3
"""Generate proof-side SMT definitions and optionally check them in Isabelle.

Requires a built ethos-eoc. Like other EOC tests, this writes shared plugin
outputs and must not run concurrently with another compiler invocation.
"""

import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", type=Path, default=ROOT / "build-eoc")
    parser.add_argument("--isabelle", default=shutil.which("isabelle"))
    parser.add_argument("--require-isabelle", action="store_true")
    parser.add_argument("--out-dir", type=Path,
                        help="Keep generated sessions here, e.g. for a separate HOL build.")
    args = parser.parse_args()
    if args.require_isabelle and not args.isabelle:
        parser.error("Isabelle is required; pass --isabelle or put it on PATH")
    with tempfile.TemporaryDirectory(prefix="eoc-isabelle-model-") as temp:
        output = args.out_dir.resolve() if args.out_dir else Path(temp)
        command = [
            sys.executable, str(HERE.parent / "driver.py"), "isabelle",
            "--build-dir", str(args.build_dir.resolve()), "--no-build",
            "--semantics", str(HERE.parent / "semantics" / "development-cpc.eos"),
            "--calc-name", "EocModel", "--final-out-dir", str(output),
            str(ROOT / "tests" / "Booleans-rules.eo"), "contra", "and_intro",
        ]
        subprocess.run(command, cwd=ROOT, check=True)
        session = output / "isabelle"

        def snapshot():
            return {str(p.relative_to(session)): p.read_bytes()
                    for p in session.rglob("*") if p.is_file()}

        checker = snapshot()
        roots = ["$eo_to_smt", "$smtx_model_eval_not", "$smtx_model_eval_and"]
        extra = [arg for root in roots for arg in ("--model-root", root)]
        subprocess.run(command + extra, cwd=ROOT, check=True)
        modeled = snapshot()
        for name, data in checker.items():
            assert modeled[name] == data, f"Model generation changed {name}"
        theory = modeled["Model/EocModel_Model.thy"].decode()
        assert 'imports "EocModel.EocModel_Checker"' in theory
        assert "datatype Term" not in theory
        assert "datatype SmtTerm" in theory
        assert "datatype SmtValue" in theory
        assert "termination by lexicographic_order" in theory
        assert "axiomatization" not in theory and "sorry" not in theory
        assert "undefined" not in theory
        assert "fuel" not in theory

        # Failed model generation must preserve the entire published package.
        for root, error in (("$missing_model_root", "Could not find target definition"),
                            ("$smtx_model_eval", "unsupported native")):
            failed = subprocess.run(command + ["--model-root", root], cwd=ROOT,
                                    text=True, capture_output=True)
            assert failed.returncode != 0, f"Unexpected support for {root}"
            assert error in failed.stderr, failed.stderr
            assert snapshot() == modeled, "Failed model generation replaced output"

        shutil.copyfile(HERE / "isabelle_model.thy", session / "Model" / "Isabelle_Model.thy")
        (session / "Model_Before.thy").write_text(
            'theory Model_Before imports EocModel_Spec begin\n'
            'export_code check_refutation in SML module_name EocChecker '
            'file_prefix checker_before\nend\n')
        with (session / "ROOT").open("a") as root:
            root.write('    Model_Before\n'
                       '  export_files (in "export") [2] "*:code/checker_before.ML"\n')
        with (session / "Model" / "ROOT").open("a") as root:
            root.write('    Isabelle_Model\n'
                       '  export_files (in "export") [2] "*:code/checker_after.ML"\n')
        if args.isabelle:
            subprocess.run([args.isabelle, "build", "-e", "-j", "1", "-o", "threads=2",
                            "-D", str(session)], check=True)
            assert ((session / "export" / "checker_before.ML").read_bytes()
                    == (session / "Model" / "export" / "checker_after.ML").read_bytes()), \
                "Adding the model changed the exported checker"
        else:
            print("Model generation passed; Isabelle unavailable, HOL checks skipped.")


if __name__ == "__main__":
    main()
