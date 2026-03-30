#!/usr/bin/env python3
"""
Unified driver for the optional Eunoia-to-SMT2/Lean compilation pipeline.

This is the canonical source-tree entrypoint for the EOC workflow.
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Optional


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_FINAL_OUT_DIR = SCRIPT_DIR / "out"
DEFAULT_CVC5 = Path("~/bin/cvc5-test").expanduser()

DECLARE_RULE_RE = re.compile(r"^\(declare-rule\s+([^\s(]+)")
INCLUDE_RE = re.compile(r'^\(include\s+"([^"]+)"\s*\)')

DESUGAR_VC_DEPS = (
    "$eot_Bool $eot_Type $eot_fun_type $eot_apply $eo_mk_apply "
    "$smtx_typeof_value $smtx_model_update $smtx_model_eval_apply"
)

LEAN_ALL_DEPS = (
    "$eot_Bool $eot_Type $eot_fun_type $eot_apply $eo_mk_apply "
    "$eo_eq $eo_ite $eo_requires $eo_and $eo_to_smt $smtx_model_eval "
    "$eo_checker_is_refutation and $eot_UConst $eot_USort "
    "$smtx_typeof $smtx_typeof_value"
)

LEAN_SINGLE_DEPS = (
    "$eot_Bool $eot_Type $eot_fun_type $eot_apply $eo_mk_apply "
    "$eo_eq $eo_ite $eo_requires $eo_and $eo_to_smt $smtx_model_eval "
    "$eo_checker_is_refutation and => $eot_UConst $eot_USort "
    "$smtx_model_eval_apply $smtx_typeof $smtx_typeof_value"
)


def resolve_path_arg(path_arg: str, *, cwd: Path) -> Path:
    candidate = Path(path_arg).expanduser()
    if candidate.is_absolute():
        return candidate.resolve()
    return (cwd / candidate).resolve()


def strip_comment(line: str) -> str:
    return line.split(";", 1)[0].strip()


def dedupe_preserve_order(items: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        ordered.append(item)
    return ordered


def discover_rules(input_file: Path) -> list[str]:
    seen_files: set[Path] = set()
    seen_rules: set[str] = set()
    ordered_rules: list[str] = []

    def visit(path: Path) -> None:
        resolved = path.resolve()
        if resolved in seen_files:
            return
        if not resolved.exists():
            raise RuntimeError(f"input file not found while scanning rules: {resolved}")
        seen_files.add(resolved)
        for raw_line in resolved.read_text().splitlines():
            line = strip_comment(raw_line)
            if not line:
                continue
            include_match = INCLUDE_RE.match(line)
            if include_match:
                include_path = resolve_path_arg(include_match.group(1), cwd=resolved.parent)
                visit(include_path)
                continue
            declare_match = DECLARE_RULE_RE.match(line)
            if declare_match:
                rule_name = declare_match.group(1)
                if rule_name not in seen_rules:
                    seen_rules.add(rule_name)
                    ordered_rules.append(rule_name)

    visit(input_file)
    return ordered_rules


def read_rules(path: Path) -> list[str]:
    rules = []
    for line in path.read_text().splitlines():
        rule = line.strip()
        if not rule or rule.startswith("#"):
            continue
        rules.append(rule)
    return rules


def replace_all(path: Path, replacements: list[tuple[str, str]]) -> None:
    text = path.read_text()
    for old, new in replacements:
        text = text.replace(old, new)
    path.write_text(text)


def inline_include(path: Path, include_name: str, include_path: Path) -> None:
    marker = f'(include "{include_name}")'
    replacement = include_path.read_text()
    text = path.read_text()
    text = text.replace(marker, replacement)
    path.write_text(text)


def splice_matching_line(path: Path, needle: str, replacement_path: Path) -> None:
    replacement = replacement_path.read_text()
    if replacement and not replacement.endswith("\n"):
        replacement += "\n"
    out_lines: list[str] = []
    for line in path.read_text().splitlines(keepends=True):
        if needle in line:
            out_lines.append(replacement)
        else:
            out_lines.append(line)
    path.write_text("".join(out_lines))


class Pipeline:
    def __init__(
        self,
        build_dir: Path,
        final_out_dir: Path,
        jobs: int,
        cvc5: Optional[Path],
    ):
        self.build_dir = build_dir.resolve()
        self.final_out_dir = final_out_dir.resolve()
        self.jobs = jobs
        self.cvc5 = cvc5
        self.binary = self.build_dir / "src" / "ethos-eoc"
        self.stage_out_dir = self.final_out_dir
        self.plugin_out_dir = self.build_dir / "out" / "plugins"

    def run(
        self,
        cmd: list[str],
        *,
        quiet: bool = False,
        cwd: Optional[Path] = None,
    ) -> None:
        stdout = subprocess.DEVNULL if quiet else None
        subprocess.run(
            cmd,
            cwd=str(cwd or self.build_dir),
            check=True,
            stdout=stdout,
        )

    def build(self) -> None:
        self.run(
            ["cmake", "--build", ".", "--target", "ethos-eoc", f"-j{self.jobs}"]
        )

    def ethos(self, args: Iterable[str], *, quiet: bool = False) -> None:
        self.run([str(self.binary), *args], quiet=quiet)

    def ensure_cvc5(self) -> Path:
        if self.cvc5 is None:
            raise RuntimeError(
                "cvc5 executable not found; pass --skip-cvc5 or --cvc5=/path/to/cvc5"
            )
        return self.cvc5

    def validate_smt(self, filename: Path, *, sygus: bool = False) -> None:
        cvc5 = self.ensure_cvc5()
        cmd = [str(cvc5), str(filename), "--parse-only"]
        if sygus:
            cmd.append("--lang=sygus")
        self.run(cmd)

    def solve_smt(self, filename: Path, *, sygus: bool = False) -> None:
        cvc5 = self.ensure_cvc5()
        cmd = [str(cvc5), str(filename)]
        if sygus:
            cmd.append("--lang=sygus")
        self.run(cmd)

    def validate_pc(self, filename: Path) -> None:
        cvc5 = self.ensure_cvc5()
        self.run([str(cvc5), str(filename), "--parse-only"])
        self.run([str(cvc5), str(filename)])

    def relative_input_from_out(self, input_name: str) -> str:
        target = Path(input_name)
        if not target.is_absolute():
            target = self.build_dir / target
        try:
            return os.path.relpath(str(target), str(self.stage_out_dir))
        except ValueError:
            return str(target)

    def binary_path_arg(self, filename: Path) -> str:
        resolved = filename.resolve()
        try:
            return str(resolved.relative_to(self.build_dir))
        except ValueError:
            return str(resolved)

    def plugin_generated(self, relative_path: str) -> Path:
        return self.plugin_out_dir / relative_path

    def stage_name(self, input_name: str) -> str:
        return Path(input_name).stem.lower()

    def trim_defs(self, input_name: str, targets: list[str], output_file: Path) -> Path:
        temp_trim = self.stage_out_dir / "temp_trim.eo"
        temp_trim.parent.mkdir(parents=True, exist_ok=True)
        pieces = [f'(include "{self.relative_input_from_out(input_name)}")\n']
        pieces.append((REPO_ROOT / "plugins" / "model_smt" / "term_reduce_deps.eo").read_text())
        if pieces[-1] and not pieces[-1].endswith("\n"):
            pieces.append("\n")
        for target in targets:
            pieces.append(f'(echo "trim-defs {target}")\n')
        temp_trim.write_text("".join(pieces))
        try:
            self.ethos(["--plugin.trim-defs", self.binary_path_arg(temp_trim)], quiet=True)
            output_file.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(self.plugin_generated("trim_defs/trim_gen.eo"), output_file)
            return output_file
        finally:
            if temp_trim.exists():
                temp_trim.unlink()

    def desugar(
        self,
        input_name: str,
        output_file: Path,
        *,
        use_vc_plugin: bool,
        deps: Optional[str],
        plugin_label: Optional[str],
    ) -> Path:
        option = "--plugin.desugar-vc" if use_vc_plugin else "--plugin.desugar"
        self.ethos([option, input_name], quiet=True)
        output_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(self.plugin_generated("desugar/eo_desugar_gen.eo"), output_file)
        replacements: list[tuple[str, str]] = []
        if deps is not None:
            replacements.append(
                ("eo-desugar-vc-deps" if use_vc_plugin else "eo-desugar-deps", deps)
            )
        if plugin_label is not None:
            replacements.append(
                ("eo-desugar-vc" if use_vc_plugin else "eo-desugar", plugin_label)
            )
        if replacements:
            replace_all(output_file, replacements)
        inline_include(
            output_file,
            "eo_builtin_smt.eo",
            self.plugin_generated("desugar/eo_builtin_smt.eo"),
        )
        inline_include(
            output_file,
            "smt_embed.eo",
            self.plugin_generated("desugar/smt_embed.eo"),
        )
        return output_file

    def model_smt(self, input_file: Path, output_file: Path) -> Path:
        self.ethos(["--plugin.model-smt", self.binary_path_arg(input_file)], quiet=True)
        output_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(input_file, output_file)
        splice_matching_line(
            output_file,
            'include eo_model_sat',
            self.plugin_generated("model_smt/model_smt_gen.eo"),
        )
        return output_file

    def smt_meta(
        self,
        input_file: Path,
        output_file: Path,
        *,
        sygus: bool,
        validate_with_cvc5: bool,
        solve_with_cvc5: bool,
    ) -> Path:
        option = "--plugin.smt-meta-sygus" if sygus else "--plugin.smt-meta"
        self.ethos([option, self.binary_path_arg(input_file)], quiet=True)
        output_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(self.plugin_generated("smt_meta/smt_meta_gen.smt2"), output_file)
        if validate_with_cvc5:
            print(f"**** smt_meta: Verify cvc5 parses {output_file}")
            self.validate_smt(output_file, sygus=sygus)
        if solve_with_cvc5:
            print(f"**** smt_meta: Run cvc5 on {output_file}")
            self.solve_smt(output_file, sygus=sygus)
        return output_file

    def lean(self, input_file: Path) -> Path:
        out_lean = self.final_out_dir / "lean"
        out_lean.mkdir(parents=True, exist_ok=True)
        self.ethos(["--plugin.lean-meta", self.binary_path_arg(input_file)], quiet=True)
        shutil.copyfile(
            self.plugin_generated("lean_meta/lean_meta_checker_gen.lean"),
            out_lean / "Logos.lean",
        )
        shutil.copyfile(
            REPO_ROOT / "plugins" / "lean_meta" / "lean_meta_smt_eval.lean",
            out_lean / "SmtEval.lean",
        )
        shutil.copyfile(
            self.plugin_generated("lean_meta/lean_meta_smt_model_gen.lean"),
            out_lean / "SmtModel.lean",
        )
        shutil.copyfile(
            self.plugin_generated("lean_meta/lean_meta_spec_gen.lean"),
            out_lean / "Spec.lean",
        )
        shutil.copyfile(
            self.plugin_generated("lean_meta/lean_meta_lemmas_gen.lean"),
            out_lean / "Lemmas.lean",
        )
        return out_lean

    def parse_file(self, filename: Path) -> None:
        self.ethos([self.binary_path_arg(filename)], quiet=True)

    def run_vc(
        self,
        input_name: str,
        target: str,
        *,
        sygus: bool,
        build_first: bool,
        validate_with_cvc5: bool,
        solve_with_cvc5: bool,
    ) -> Path:
        if build_first:
            self.build()
        stem = self.stage_name(input_name)
        init_trim = self.stage_out_dir / f"trim-{stem}.eo"
        init_desugar = self.stage_out_dir / f"trim-d-{stem}.eo"
        vcm_defs = self.stage_out_dir / f"vcm-def-{stem}.eo"
        vcmt_defs = self.stage_out_dir / f"vcmt-def-{stem}.eo"
        suffix = "sy" if sygus else "smt2"
        final_out = self.final_out_dir / ("sygus" if sygus else "vc") / f"final-{stem}-{target}.{suffix}"

        print(
            f"********* {'Searching for counterexamples of' if sygus else 'Verifying the correctness of'} {target} {'via sygus' if sygus else 'via smt2'} *********"
        )
        print(f"**** smt_meta: Run ethos + trim-defs on {input_name} and {target} to {init_trim}")
        self.trim_defs(input_name, [target], init_trim)
        print(f"**** smt_meta: Run ethos + desugar on {init_trim} to generate {init_desugar}")
        self.desugar(
            self.binary_path_arg(init_trim),
            init_desugar,
            use_vc_plugin=True,
            deps=DESUGAR_VC_DEPS,
            plugin_label="smt-meta",
        )
        print(f"**** smt_meta: Run ethos + model-smt on {init_desugar} to generate {vcm_defs}")
        self.model_smt(init_desugar, vcm_defs)
        print(f"**** smt_meta: Run ethos + trim-deps on {vcm_defs} to generate {vcmt_defs}")
        self.trim_defs(self.binary_path_arg(vcm_defs), [f"$eovc_{target}"], vcmt_defs)
        print("**** smt_meta: Verify ethos parses")
        self.parse_file(vcmt_defs)
        if sygus:
            print(f"**** smt_meta: Generate sygus from {vcmt_defs} to {final_out}")
        else:
            print(f"**** smt_meta: Generate SMT2 from {vcmt_defs} to {final_out}")
        self.smt_meta(
            vcmt_defs,
            final_out,
            sygus=sygus,
            validate_with_cvc5=validate_with_cvc5,
            solve_with_cvc5=solve_with_cvc5,
        )
        return final_out

    def run_lean(
        self,
        input_name: str,
        targets: list[str],
        *,
        all_targets: bool,
        build_first: bool,
    ) -> Path:
        if build_first:
            self.build()
        stem = self.stage_name(input_name)
        print(
            f"********* Generating Lean for {input_name if all_targets else ' '.join(targets) + ' in ' + input_name} *********"
        )
        if all_targets:
            init_desugar = self.stage_out_dir / f"lean-{stem}-desugar.eo"
            final_defs = self.stage_out_dir / f"lean-{stem}-final.eo"
            print(f"**** lean_meta: Run ethos + desugar on {input_name} to generate {init_desugar}")
            self.desugar(
                input_name,
                init_desugar,
                use_vc_plugin=False,
                deps=LEAN_ALL_DEPS,
                plugin_label="lean-meta",
            )
            print(f"**** lean_meta: Run ethos + model-smt on {init_desugar} to generate {final_defs}")
            self.model_smt(init_desugar, final_defs)
            print("**** lean_meta: Verify ethos parses")
            self.parse_file(final_defs)
            print(f"**** lean_meta: Generate Lean from {final_defs} to {self.final_out_dir / 'lean'}")
            return self.lean(final_defs)

        init_trim = self.stage_out_dir / f"lean-{stem}-trim.eo"
        init_desugar = self.stage_out_dir / f"lean-{stem}-desugar.eo"
        vcm_defs = self.stage_out_dir / f"lean-{stem}-defs.eo"
        final_defs = self.stage_out_dir / f"lean-{stem}-final.eo"
        print(
            f'**** lean_meta: Run ethos + trim-defs on {input_name} and "{" ".join(targets)}" to {init_trim}'
        )
        self.trim_defs(input_name, list(targets) + ["and", "=>"], init_trim)
        print(f"**** lean_meta: Run ethos + desugar on {init_trim} to generate {init_desugar}")
        self.desugar(
            self.binary_path_arg(init_trim),
            init_desugar,
            use_vc_plugin=False,
            deps=LEAN_SINGLE_DEPS,
            plugin_label="lean-meta",
        )
        print(f"**** lean_meta: Run ethos + model-smt on {init_desugar} to generate {vcm_defs}")
        self.model_smt(init_desugar, vcm_defs)
        target_progs = [f"$eo_prog_{target}" for target in targets]
        print(f"**** lean_meta: Run ethos + trim-deps on {vcm_defs} to generate {final_defs}")
        self.trim_defs(self.binary_path_arg(vcm_defs), target_progs, final_defs)
        print("**** lean_meta: Verify ethos parses")
        self.parse_file(final_defs)
        print(f"**** lean_meta: Generate Lean from {final_defs} to {self.final_out_dir / 'lean'}")
        return self.lean(final_defs)

    def run_desugar(self, input_name: str, *, build_first: bool) -> Path:
        if build_first:
            self.build()
        output = self.final_out_dir / "desugar.eo"
        print(f"**** smt_meta: Run ethos + desugar on {input_name} to generate {output}")
        self.desugar(input_name, output, use_vc_plugin=True, deps=None, plugin_label=None)
        print("**** smt_meta: Verify it parses")
        self.parse_file(output)
        return output

    def run_pc_valid(
        self,
        input_name: str,
        *,
        build_first: bool,
        validate_with_cvc5: bool,
    ) -> Path:
        if build_first:
            self.build()
        init_desugar = self.stage_out_dir / "desugar-pcv.eo"
        input_file = Path(input_name)
        final_out = self.final_out_dir / "pcv" / f"check-{input_file.name}.smt2"
        print(f"********* Validating equivalence of proof checking for {input_name} *********")
        print(f"**** smt_meta: Run ethos + desugar on {input_name} to generate {init_desugar}")
        self.desugar(input_name, init_desugar, use_vc_plugin=False, deps=None, plugin_label=None)
        print(f"**** smt_meta: Generate SMT2 from {init_desugar} to {final_out}")
        self.smt_meta(init_desugar, final_out, sygus=False, validate_with_cvc5=False)
        if validate_with_cvc5:
            print("**** smt_meta: Verify cvc5 parses")
            self.validate_pc(final_out)
        return final_out

    def run_trim_only(self, input_name: str, targets: list[str], *, build_first: bool) -> Path:
        if build_first:
            self.build()
        output = self.final_out_dir / "trim_defs" / "trim_gen.eo"
        print(f"**** run_trim_defs: Run ethos + trim-defs on {input_name}")
        self.trim_defs(input_name, targets, output)
        return output

    def clean_final_dir(self, mode: str) -> None:
        target_dir = self.final_out_dir / mode
        if not target_dir.exists():
            return
        for child in target_dir.iterdir():
            if child.is_file():
                child.unlink()


def resolve_cvc5(path_arg: Optional[str], *, cwd: Path) -> Optional[Path]:
    if path_arg:
        candidate = resolve_path_arg(path_arg, cwd=cwd)
        return candidate if candidate.exists() else None
    env_path = os.environ.get("CVC5")
    if env_path:
        candidate = resolve_path_arg(env_path, cwd=cwd)
        return candidate if candidate.exists() else None
    return DEFAULT_CVC5 if DEFAULT_CVC5.exists() else None


def add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--build-dir",
        default=os.getcwd(),
        help="Build directory containing src/ethos-eoc and out/.",
    )
    parser.add_argument(
        "--final-out-dir",
        default=None,
        help="Directory for final published outputs. Defaults to $EOC_FINAL_OUT_DIR or tools/eoc/out.",
    )
    parser.add_argument("--jobs", type=int, default=4, help="Parallel build jobs.")
    parser.add_argument(
        "--cvc5",
        default=None,
        help="Path to cvc5 for parse/validation checks. Defaults to $CVC5 or ~/bin/cvc5-test.",
    )
    parser.add_argument(
        "--skip-cvc5",
        action="store_true",
        help="Skip cvc5 parse/validation checks.",
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Do not rebuild ethos-eoc before running the pipeline.",
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    vc = subparsers.add_parser("vc", help="Generate an SMT2 or SyGuS VC for one rule.")
    add_common_args(vc)
    vc.add_argument("input")
    vc.add_argument("target")
    vc.add_argument("--sygus", action="store_true")
    vc.add_argument(
        "--solve",
        action="store_true",
        help="Run cvc5 on the generated VC or SyGuS file after optional parse checks.",
    )

    lean = subparsers.add_parser("lean", help="Generate Lean output for selected rules.")
    add_common_args(lean)
    lean.add_argument("input")
    lean.add_argument("targets", nargs="*")
    lean.add_argument("--all", action="store_true", help="Compile the entire signature.")

    desugar = subparsers.add_parser("desugar", help="Generate a desugared EO file.")
    add_common_args(desugar)
    desugar.add_argument("input")

    pc_valid = subparsers.add_parser(
        "pc-valid", help="Generate and optionally validate a proof-checking SMT query."
    )
    add_common_args(pc_valid)
    pc_valid.add_argument("input")

    trim = subparsers.add_parser("trim-defs", help="Run the trim-defs plugin only.")
    add_common_args(trim)
    trim.add_argument("input")
    trim.add_argument("targets", nargs="+")

    list_rules = subparsers.add_parser(
        "list-rules", help="Print declared rules from a signature and its includes."
    )
    list_rules.add_argument("input")

    batch = subparsers.add_parser("batch", help="Run a set of rules through a pipeline.")
    add_common_args(batch)
    batch.add_argument("mode", choices=["vc", "sygus"])
    batch.add_argument("input")
    batch.add_argument("rules", nargs="*")
    batch.add_argument(
        "--all-rules",
        action="store_true",
        help="Discover all declared rules from the input signature recursively.",
    )
    batch.add_argument("--rules-file")
    batch.add_argument("--clean", action="store_true", help="Delete existing final outputs first.")
    batch.add_argument(
        "--solve",
        action="store_true",
        help="Run cvc5 on each generated VC or SyGuS file after optional parse checks.",
    )
    batch.add_argument(
        "--keep-going",
        action="store_true",
        help="Continue after a failing rule and report all failures.",
    )

    args = parser.parse_args(argv)
    invocation_cwd = Path.cwd().resolve()

    if hasattr(args, "input"):
        args.input = str(resolve_path_arg(args.input, cwd=invocation_cwd))
    if getattr(args, "rules_file", None) is not None:
        args.rules_file = str(resolve_path_arg(args.rules_file, cwd=invocation_cwd))

    if getattr(args, "final_out_dir", None) is not None:
        final_out_dir = resolve_path_arg(args.final_out_dir, cwd=invocation_cwd)
    else:
        final_out_env = os.environ.get("EOC_FINAL_OUT_DIR")
        if final_out_env:
            final_out_dir = resolve_path_arg(final_out_env, cwd=invocation_cwd)
        else:
            final_out_dir = DEFAULT_FINAL_OUT_DIR

    need_cvc5 = not getattr(args, "skip_cvc5", False) or getattr(args, "solve", False)
    cvc5 = resolve_cvc5(getattr(args, "cvc5", None), cwd=invocation_cwd) if need_cvc5 else None
    pipeline = Pipeline(
        Path(getattr(args, "build_dir", os.getcwd())),
        final_out_dir,
        getattr(args, "jobs", 4),
        cvc5,
    )
    build_first = not getattr(args, "no_build", False)

    try:
        if args.command == "vc":
            pipeline.run_vc(
                args.input,
                args.target,
                sygus=args.sygus,
                build_first=build_first,
                validate_with_cvc5=not args.skip_cvc5,
                solve_with_cvc5=args.solve,
            )
        elif args.command == "lean":
            if not args.all and not args.targets:
                parser.error("lean requires at least one target unless --all is passed")
            pipeline.run_lean(
                args.input,
                list(args.targets),
                all_targets=args.all,
                build_first=build_first,
            )
        elif args.command == "desugar":
            pipeline.run_desugar(args.input, build_first=build_first)
        elif args.command == "trim-defs":
            pipeline.run_trim_only(
                args.input,
                list(args.targets),
                build_first=build_first,
            )
        elif args.command == "list-rules":
            for rule in discover_rules(Path(args.input)):
                print(rule)
        else:
            rules: list[str] = []
            if args.all_rules:
                rules.extend(discover_rules(Path(args.input)))
            if args.rules_file is not None:
                rules.extend(read_rules(Path(args.rules_file)))
            rules.extend(args.rules)
            rules = dedupe_preserve_order(rules)
            if not rules:
                parser.error("batch requires at least one rule, --rules-file, or --all-rules")
            if build_first:
                pipeline.build()
            if args.clean:
                pipeline.clean_final_dir("sygus" if args.mode == "sygus" else "vc")
            failures: list[str] = []
            for rule in rules:
                print(f"==== {rule}")
                try:
                    pipeline.run_vc(
                        args.input,
                        rule,
                        sygus=args.mode == "sygus",
                        build_first=False,
                        validate_with_cvc5=not args.skip_cvc5,
                        solve_with_cvc5=args.solve,
                    )
                except subprocess.CalledProcessError:
                    failures.append(rule)
                    if not args.keep_going:
                        raise
            if failures:
                print("Failed rules:")
                for rule in failures:
                    print(f"  {rule}")
                return 1
        return 0
    except subprocess.CalledProcessError as err:
        return err.returncode
    except RuntimeError as err:
        print(err, file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
