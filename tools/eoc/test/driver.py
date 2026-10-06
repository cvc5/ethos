#!/usr/bin/env python3
"""Exercise rule listing and selection of semantics across builds."""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


EOC = Path(__file__).resolve().parents[1]


class RuleListing(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        # A listing must need only the driver, its output helper, and input.
        # In particular, sem_compile.py and plugins/ are deliberately absent.
        for source in (EOC / "driver.py", EOC / "compiler" / "report.py"):
            shutil.copyfile(source, self.root / source.name)

    def run_listing(self, name):
        return subprocess.run(
            [sys.executable, "-B", str(self.root / "driver.py"),
             "list-rules", name],
            cwd=self.root, capture_output=True, text=True,
        )

    def test_includes_order_and_duplicates(self):
        (self.root / "main.eo").write_text(
            '(declare-rule first () :conclusion true)\n'
            '(include "nested.eo")\n'
            '(declare-rule last () :conclusion true)\n'
        )
        (self.root / "nested.eo").write_text(
            '(declare-rule nested () :conclusion true)\n'
            '(include "main.eo")\n'
            '(declare-rule first () :conclusion true)\n'
        )
        before = {p.name: p.read_bytes() for p in self.root.iterdir()}
        result = self.run_listing("main.eo")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "first\nnested\nlast\n")
        self.assertEqual(result.stderr, "")
        self.assertEqual(
            {p.name: p.read_bytes() for p in self.root.iterdir()}, before)

    def test_missing_include_is_a_diagnostic(self):
        (self.root / "main.eo").write_text('(include "missing.eo")\n')
        result = self.run_listing("main.eo")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertIn("error: input file not found", result.stderr)
        self.assertNotIn("Traceback", result.stderr)

    def test_directory_is_a_diagnostic(self):
        result = self.run_listing(".")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertIn("error:", result.stderr)
        self.assertNotIn("Traceback", result.stderr)


class SemanticsSelection(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        sys.path.insert(0, str(EOC))
        import driver
        import sem_compile
        cls.driver = driver
        cls.compiler = sem_compile

    def test_selected_semantics_survive_build(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            semantics = root / "Custom.eos"
            shutil.copyfile(EOC / "test" / "semantics.eos", semantics)
            smt_semantics = root / "CustomSmt.eos"
            shutil.copyfile(EOC / "semantics" / "smt.eos", smt_semantics)
            binary = root / "ethos-eoc"
            binary.touch()
            explicit_lean = root / "explicit.lean"
            explicit_lean.write_text("-- caller's termination clauses\n")
            compile_sets = self.compiler.compile_to_files

            def build(pipeline):
                # CMake regenerates the shipped sets in the same locations
                # used by the selected sets. Model that overwrite directly.
                compile_sets(out_dir=str(root))

            def selected_sets(sets):
                return compile_sets(sets, out_dir=str(root))

            def run(pipeline, *args, **kwargs):
                self.assertFalse(kwargs["build_first"])
                for path in (pipeline.defs_file, pipeline.desugar_defs):
                    self.assertIn("Custom.eos", path.read_text())
                self.assertIn("CustomSmt.eos", pipeline.smt_defs_file.read_text())
                if override_lean:
                    self.assertEqual(pipeline.lean_config, explicit_lean)
                else:
                    self.assertIn("Custom.eos", pipeline.lean_config.read_text())

            commands = (
                (["vc", "input.eo", "rule"], "run_vc"),
                (["lean", "input.eo", "rule"], "run_lean"),
                (["desugar", "input.eo"], "run_desugar"),
                (["trim-defs", "input.eo", "rule"], "run_trim_only"),
                (["batch", "vc", "input.eo", "rule"], "run_vc"),
            )
            for command, method in commands:
                for no_build, override_lean in ((False, False), (True, True)):
                    with self.subTest(command=command[0], no_build=no_build):
                        options = ["--build-dir", str(root), "--skip-cvc5",
                                   "--semantics", str(semantics),
                                   "--smt-semantics", str(smt_semantics)]
                        if no_build:
                            options.append("--no-build")
                        if override_lean:
                            options.extend(["--lean-config", str(explicit_lean)])
                        with mock.patch.object(self.driver.Pipeline, "build",
                                               autospec=True, side_effect=build) as built, \
                             mock.patch.object(self.compiler, "compile_to_files",
                                               side_effect=selected_sets), \
                             mock.patch.object(self.driver.Pipeline, method,
                                               autospec=True, side_effect=run):
                            self.assertEqual(self.driver.main(command + options), 0)
                            self.assertEqual(built.call_count, int(not no_build))


if __name__ == "__main__":
    unittest.main()
