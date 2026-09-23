#!/usr/bin/env python3
"""Exercise rule listing without a build or generated semantics."""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


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


if __name__ == "__main__":
    unittest.main()
