#!/usr/bin/env python3
"""Generate checker sessions and, when available, execute their HOL tests.

  python3 tools/eoc/test/isabelle.py --build-dir build-eoc --isabelle /path/to/isabelle

The C++ binary must already be built. --require-isabelle makes an absent
Isabelle installation an error (appropriate for a job claiming HOL coverage).
"""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
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
                  "distinct_names", "indexed_rule", "native_arith", "native_compare",
                  "native_strings", "native_extract", "native_convert", "native_bits",
                  "mutual_rule", "arith-elim-int-gt", "arith_elim_int_gt",
                  "arith_elim_int_gt_2", "checker_is_refutation", "parameter_names",
                  "operator_names", "conjunction", "negate", "negative_constant",
                  "string_constant", "chained", "gather"],
                 out / "selected", "EocTest")
        session = out / "selected" / "isabelle"
        checker = (session / "EocTest_Checker.thy").read_text()
        spec = (session / "EocTest_Spec.thy").read_text()
        runtime = session / "Runtime"
        syntax = json.loads((runtime / "syntax.json").read_text())
        ops = {entry['name']: entry for entry in syntax['operators']}
        assert ops['conjunction']['arity'] == ops['and']['arity'] == 'right-assoc-nil'
        assert ops['conjunction']['head'] == ops['and']['head']
        assert ops['indexed']['indices'] == 1
        assert ops['chained']['connector'] == ops['gather']['connector'] == 'or'
        assert ops['a b']['head'] != ops['a_x20b']['head']
        assert 'negate' in {entry['name'] for entry in syntax['definitions']}
        assert 'contra' in {entry['name'] for entry in syntax['rules']}
        assert '$TYPEOF$' not in (runtime / 'Parser.ML').read_text()
        assert '$NIL$' not in (runtime / 'Parser.ML').read_text()
        for name in ("arith_elim_int_gt", "arith_elim_int_gt_2",
                     "arith_elim_int_gt_2_2", "and_intro", "parameter_names"):
            assert f"primrec p_{name} ::" in checker, name
            assert f"definition obligation_{name} where" in spec, name
            assert f"p_{name} fuel" in spec, name
        assert "CCmd_assume_push" in checker
        assert "Term_Op_implies" in checker
        assert "p__x24eo" not in checker and "_x5f" not in checker
        programs = re.findall(r"^(?:primrec|abbreviation) (p_\w+) ", checker, re.M)
        assert len(programs) == len(set(programs)), "duplicate program names"
        # Catch stale or missing public names even on generation-only CI jobs.
        symbol = r"\b(?:p_|Term_Op_|CRule_|CCmd_|UserOp\d*_Op_)\w+"
        referenced = set(re.findall(symbol, (HERE / "isabelle_smoke.thy").read_text()))
        generated = set(re.findall(symbol, checker))
        assert referenced <= generated, sorted(referenced - generated)
        # The rule took the helper's preferred name: the public checker must
        # still call the actual helper, using its allocated suffix.
        assert "(p_checker_is_refutation_2 fuel assumptions commands = Some True)" in checker
        shutil.copyfile(HERE / "isabelle_smoke.thy", session / "Isabelle_Smoke.thy")
        with (session / "ROOT").open("a") as root:
            root.write("    Isabelle_Smoke\n")
        shutil.copyfile(HERE / "isabelle_parser.thy", session / "Isabelle_Parser.thy")
        with (session / "ROOT").open("a") as root:
            root.write('    Isabelle_Parser\n'
                       '  export_files (in "export") [2] "*:code/cpc.ML"\n')
        root = session / "ROOT"
        root.write_text(root.read_text().replace('  theories\n',
                        '  sessions "HOL-Library"\n  theories\n'))
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
        # Exercise the real installer, including paths with spaces, repeat
        # installation, preserving handwritten files, and failure isolation.
        iogos = out / "iogos checkout"
        (iogos / "Cpc").mkdir(parents=True)
        handwritten = iogos / "Cpc" / "Handwritten.thy"
        handwritten.write_text("handwritten proof placeholder\n")
        (iogos / "Cpc" / "Runtime").mkdir()
        runtime_build = iogos / "Cpc" / "Runtime" / "Runtime_Export.thy"
        runtime_build.write_text("handwritten runtime export\n")
        (iogos / "Cpc" / "Runtime" / "Parser.ML").write_text("stale parser\n")
        roots = iogos / "ROOTS"
        roots.write_text("# existing session list")  # no trailing newline
        env = dict(os.environ, BUILD_DIR=str(args.build_dir.resolve()),
                   EOC_NO_BUILD="1", EOC_CPC_INPUT=str(HERE / "isabelle.eo"),
                   EOC_SEMANTICS="", EOC_FINAL_OUT_DIR=str(out / "install output"),
                   IOGOS_DIR=str(iogos))
        installer = str(HERE.parent / "cpc" / "install_iogos")
        for _ in range(2):
            subprocess.run([installer], cwd=out, env=env, check=True)
        assert roots.read_text() == "# existing session list\nCpc\n"
        assert handwritten.read_text() == "handwritten proof placeholder\n"
        installed = (iogos / "Cpc" / "Cpc_Checker.thy").read_bytes()
        assert installed.count(b"Auto-generated by ethos") == 1
        installed_runtime = {name: (iogos / 'Cpc' / 'Runtime' / name).read_bytes()
                             for name in ('Parser.ML', 'Sexp.ML', 'syntax.json',
                                          'generate_syntax.py')}
        assert installed_runtime['Parser.ML'].count(b'Auto-generated by ethos') == 1
        assert b'stale parser' not in installed_runtime['Parser.ML']
        assert runtime_build.read_text() == "handwritten runtime export\n"
        failed = subprocess.run([installer], cwd=out,
                                env=dict(env, EOC_CPC_INPUT=str(unsupported)),
                                capture_output=True, text=True)
        assert failed.returncode != 0
        assert (iogos / "Cpc" / "Cpc_Checker.thy").read_bytes() == installed
        assert roots.read_text() == "# existing session list\nCpc\n"
        for name, data in installed_runtime.items():
            assert (iogos / 'Cpc' / 'Runtime' / name).read_bytes() == data
        if args.isabelle:
            subprocess.run([args.isabelle, "build", "-e", "-j", "2", "-o", "threads=2",
                            "-D", str(session), "-D", str(out / "all" / "isabelle")],
                           check=True)
            export = session / "export" / "cpc.ML"
            module_spec = importlib.util.spec_from_file_location(
                'generate_syntax', runtime / 'generate_syntax.py')
            binder = importlib.util.module_from_spec(module_spec)
            module_spec.loader.exec_module(binder)
            bound = binder.generate(checker, syntax, export.read_text())
            frontend = session / 'Parser_Test.ML'
            frontend.write_text(export.read_text() + '\n' + bound + '\n'
                                + (runtime / 'Sexp.ML').read_text() + '\n'
                                + (runtime / 'Parser.ML').read_text() + '\n'
                                + (HERE / 'isabelle_parser.ML').read_text())
            def getenv(name):
                return subprocess.check_output([args.isabelle, 'getenv', '-b', name],
                                               text=True).strip()
            poly = Path(getenv('POLYML_HOME')) / getenv('ISABELLE_PLATFORM64') / 'poly'
            subprocess.run([str(poly), '-q', '--error-exit', '--use', str(frontend)],
                           check=True)
        else:
            print("Generation passed; Isabelle unavailable, HOL execution skipped.")


if __name__ == "__main__":
    main()
