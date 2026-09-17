#!/usr/bin/env python3
"""Generate checker sessions and, when available, execute their HOL tests.

  python3 tools/eoc/test/isabelle.py --build-dir build-eoc --isabelle /path/to/isabelle

The C++ binary must already be built. --require-isabelle makes an absent
Isabelle installation an error (appropriate for a job claiming HOL coverage).
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
    args = parser.parse_args()
    if args.require_isabelle and not args.isabelle:
        parser.error("Isabelle is required; pass --isabelle or put it on PATH")
    with tempfile.TemporaryDirectory(prefix="eoc-isabelle-test-") as temp:
        out = Path(temp)

        def generate(signature, extra, directory, name):
            subprocess.run([
                sys.executable, str(HERE.parent / "driver.py"), "isabelle",
                "--build-dir", str(args.build_dir.resolve()), "--no-build",
                "--final-out-dir", str(directory), "--calc-name", name,
                str(signature), *extra,
            ], cwd=ROOT, check=True)

        generate(HERE / "isabelle.eo",
                 ["contra", "and_intro", "truth", "selection", "zero", "diverge", "lazy", "scope",
                  "distinct_names"],
                 out / "selected", "EocTest")
        session = out / "selected" / "isabelle"
        shutil.copyfile(HERE / "isabelle_smoke.thy", session / "Isabelle_Smoke.thy")
        with (session / "ROOT").open("a") as root:
            root.write("    Isabelle_Smoke\n")
        # A missing native must fail before replacing the published session.
        before = (session / "EocTest_Checker.thy").read_bytes()
        unsupported = out / "unsupported.eo"
        unsupported.write_text(
            '(declare-const Int Type)\n(declare-consts <numeral> Int)\n'
            '(declare-rule hash_rule ((x Bool)) :args (x)\n'
            '  :conclusion (eo::eq (eo::hash x) 0))\n')
        failed = subprocess.run([
            sys.executable, str(HERE.parent / "driver.py"), "isabelle",
            "--build-dir", str(args.build_dir.resolve()), "--no-build",
            "--final-out-dir", str(out / "selected"), "--calc-name", "EocTest",
            str(unsupported), "--all",
        ], cwd=ROOT, capture_output=True, text=True)
        assert failed.returncode != 0, "unsupported native was accepted"
        assert "unsupported native thash" in failed.stderr, failed.stderr
        assert (session / "EocTest_Checker.thy").read_bytes() == before
        generate(ROOT / "tests" / "Booleans-rules.eo", ["--all"],
                 out / "all", "EocAll")
        if args.isabelle:
            subprocess.run([args.isabelle, "build", "-j", "2", "-o", "threads=2",
                            "-D", str(session), "-D", str(out / "all" / "isabelle")],
                           check=True)
        else:
            print("Generation passed; Isabelle unavailable, HOL execution skipped.")


if __name__ == "__main__":
    main()
