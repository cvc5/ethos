#!/usr/bin/env python3
"""Generate, compile, lint and execute an independent parser-free checker."""
import argparse
import csv
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-dir", default=ROOT / "build-eoc", type=Path)
    parser.add_argument("--cargo", default="cargo")
    parser.add_argument("--cpc", type=Path,
                        help="Use CPC, with sibling Cpc.eos and smt.eos, instead of the small fixture.")
    parser.add_argument("--debug-only", action="store_true")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="ethos-rust-meta-") as temp:
        out = Path(temp)
        signature = args.cpc.resolve() if args.cpc else Path(__file__).with_name("signature.eo")
        if args.cpc:
            checks = signature.parents[2] / "Cpc/TranslationChecks.lean"
            if checks.is_file():
                text = checks.read_text().split("def cmdTranslationOk : CCmd -> Prop", 1)[1]
                text = text.split("/--", 1)[0]
                masks = [rule + " " + " ".join(re.findall(r"ArgTranslationKind\.(\w+)", mask))
                         for rule, mask in re.findall(
                             r"\| CCmd.step CRule\.(\w+) args _ =>\s*cArgListTranslationOkMask \[(.*?)\] args",
                             text, re.S)]
                expected = (ROOT / "plugins/rust_meta/cpc_translation_masks.txt").read_text()
                expected = [line for line in expected.splitlines() if line and not line.startswith("#")]
                assert masks == expected, "CPC translation masks differ from the selected Logos checkout"
        semantics = (["--semantics", str(signature.parent / "Cpc.eos"),
                      "--smt-semantics", str(signature.parent / "smt.eos")]
                     if args.cpc else [])
        subprocess.run([sys.executable, str(ROOT / "tools/eoc/driver.py"),
                        "rust", "--build-dir", str(args.build_dir.resolve()),
                        "--no-build", "--final-out-dir", str(out),
                        *semantics, str(signature)], check=True)
        crate = out / "rust"
        (crate / "tests").mkdir()
        tests = Path(__file__).with_name("checker.rs").read_text()
        if args.cpc:
            tests = tests.split("#[test]\nfn nonlinear_patterns_requirements_and_lazy_branches")[0]
            (crate / "tests/cpc.rs").write_text(Path(__file__).with_name("cpc.rs").read_text())
        (crate / "tests/checker.rs").write_text(tests)
        source = (crate / "src/generated.rs").read_text()
        assert '"$eo_invoke_assume_list", compiled to an iterative guarded fold' in source
        with (crate / "caches.tsv").open() as f:
            policies = {row["source"]: row["cache"] for row in csv.DictReader(f, delimiter="\t")}
        assert policies["$eo_typeof"] == "eo-type"
        assert policies["$eo_invoke_cmd_list"] == "none"
        if args.cpc:
            assert policies["$smtx_typeof"] == "smt-type"
        else:
            for name in ["$eo_prog_dag", "$eo_prog_dag_false", "$eo_prog_swap",
                         "$eo_prog_mutual_a", "$eo_prog_mutual_b"]:
                assert policies[name] == "program", name
            assert policies["$eo_prog_nonlin"] == "none"
        assert 's.builtin(EvalOp::Add' in source or 's.builtin(EvalOp::ListConcat' in source
        assert "EO program \"$eo_add\"" not in source
        assert not any(p.name.lower().startswith("parser") for p in crate.rglob("*"))
        env = os.environ.copy()
        # Reuse compiled dependencies between invocations, without leaving
        # generated source or test results in the checked-in resource tree.
        env.setdefault("CARGO_TARGET_DIR", str(args.build_dir.resolve() / "rust-meta-target"))
        commands = [
            ["fmt", "--all"],
            ["clippy", "--locked", "--all-targets", "--", "-D", "warnings"],
            ["test", "--locked"],
        ]
        if not args.debug_only:
            commands.append(["test", "--locked", "--release"])
        for command in commands:
            subprocess.run([args.cargo, *command], cwd=crate, env=env, check=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
