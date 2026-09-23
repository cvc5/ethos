#!/usr/bin/env python3
"""Generate CPC and check parametric datatypes against Logos's parDt parser.

The Logos checkout is read only. Generated modules and a temporary Lake package
are written under --out-dir (or a temporary directory). Like the other EOC
integration tests, generation must not run concurrently with another EOC run.
"""

import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def run(args, output):
    logos = args.logos.resolve()
    for path in (logos / "Logos/Parser.lean", logos / "install/defs/Cpc.cached.eo",
                 logos / "install/defs/Cpc.eos", logos / "lean-toolchain"):
        if not path.is_file():
            raise SystemExit(f"Missing Logos input: {path}")
    if "mkParam" not in (logos / "Logos/Parser.lean").read_text():
        raise SystemExit("The Logos parser must include the parDt datatype hooks")
    generated = output / "generated"
    if not args.no_generate:
        subprocess.run([
            sys.executable, str(HERE.parent / "driver.py"), "lean", "--all",
            "--build-dir", str(args.build_dir.resolve()), "--no-build",
            "--semantics", str(logos / "install/defs/Cpc.eos"),
            "--calc-name", "Cpc", "--final-out-dir", str(generated),
            str(logos / "install/defs/Cpc.cached.eo"),
        ], cwd=ROOT, check=True)
    if not (generated / "lean/LogosTerm.lean").is_file():
        raise SystemExit(f"No generated CPC modules under {generated / 'lean'}")
    package = output / "check"
    package.mkdir(parents=True, exist_ok=True)
    shutil.copytree(logos / "Logos", package / "Logos", dirs_exist_ok=True)
    (package / "Cpc").mkdir(exist_ok=True)
    for module in (generated / "lean").glob("*.lean"):
        shutil.copyfile(module, package / "Cpc" / module.name)
    shutil.copyfile(logos / "lean-toolchain", package / "lean-toolchain")
    (package / "lakefile.toml").write_text(
        'name = "EocParametricTest"\n[[lean_lib]]\nname = "Logos"\n'
        '[[lean_lib]]\nname = "Cpc"\n')
    shutil.copyfile(HERE / "parametric_datatypes.lean", package / "Test.lean")
    subprocess.run([args.lake, "build", "Cpc.Parser", "Cpc.Spec"], cwd=package, check=True)
    subprocess.run([args.lake, "env", "lean", "Test.lean"], cwd=package, check=True)
    print("Parametric datatype parsing, typing, rules and translation passed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--logos", type=Path, default=Path.home() / "logos")
    parser.add_argument("--build-dir", type=Path, default=ROOT / "build-eoc")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--out-dir", type=Path, help="Keep generated modules and Lake build")
    parser.add_argument("--no-generate", action="store_true",
                        help="Reuse --out-dir/generated from an earlier run")
    args = parser.parse_args()
    if args.no_generate and not args.out_dir:
        parser.error("--no-generate requires --out-dir")
    if args.out_dir:
        run(args, args.out_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="eoc-parametric-") as temp:
            run(args, Path(temp))


if __name__ == "__main__":
    main()
