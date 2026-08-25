#!/usr/bin/env python3
"""
Unified driver for the optional Eunoia-to-Lean compilation pipeline.

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
LEAN_CALC_PLACEHOLDER = "$EO_CALC$"

# The signature-wide Lean files written by the lean subcommand, in module
# dependency order. Each entry is (source relative to plugins/, name written
# under <final out dir>/lean, whether the source is rendered by the Lean
# backend rather than copied verbatim from the plugin source tree). The
# per-rule files under lean/Rules/ are published separately, see
# publish_generated_lean_rule_outputs.
#
# <final out dir>/lean is what a run publishes, not a Lean package that builds
# on its own: the generated modules import <Calc>.Proofs.CheckerCore and
# <Calc>.Proofs.RuleSupport.Support, which the compiler never writes and which
# belong to the package the files are installed into. That package holds the
# proof-side modules under Proofs/, and the published tree is it with that one
# component dropped, uniformly: RuleLemmas.lean is installed as
# Proofs/RuleLemmas.lean and Rules/<Rule>.lean as Proofs/Rules/<Rule>.lean,
# which is what the import <Calc>.Proofs.Rules.<Rule> lines that the former
# carries name. Everything else is installed at the root of the package, where
# its name already is its import.
LEAN_OUTPUTS: tuple[tuple[str, str, bool], ...] = (
    ("lean_meta/lean_meta_checker_gen.lean", "Logos.lean", True),
    ("lean_meta/lean_meta_checker_term_gen.lean", "LogosTerm.lean", True),
    ("lean_meta/lean_meta_parser_gen.lean", "Parser.lean", True),
    ("lean_meta/lean_meta_smt_eval.lean", "SmtEval.lean", False),
    ("lean_meta/lean_meta_smt_model_defs_gen.lean", "SmtModelDefs.lean", True),
    ("lean_meta/lean_meta_smt_value_order_gen.lean", "SmtValueOrder.lean", True),
    ("lean_meta/lean_meta_smt_model_gen.lean", "SmtModel.lean", True),
    ("lean_meta/lean_meta_spec_gen.lean", "Spec.lean", True),
    ("lean_meta/lean_meta_rule_lemmas_gen.lean", "RuleLemmas.lean", True),
)

DECLARE_RULE_RE = re.compile(r"^\(declare-rule\s+([^\s(]+)")
INCLUDE_RE = re.compile(r'^\(include\s+"([^"]+)"\s*\)')
# Any directive a block of a signature written in the deep embedding gives to a
# stage of the compiler, rather than something it says about the model.
DEFS_DIRECTIVE = re.compile(r'\(echo\s+"[^"]*"\)')
# The one of those that leaves what it names out of the compilation altogether.
DEFS_EXCLUDE = re.compile(r'\(echo\s+"eoc-exclude\s+(\S+)\s+(\S+)"\s*\)')

LEAN_ALL_DEPS = (
    "$eot_Bool $eot_Type $eot_fun_type $eot_apply $eo_mk_apply "
    "$eo_eq $eo_ite $eo_requires $eo_and $eo_to_smt $smtx_model_eval "
    "$eo_checker_is_refutation and $eot_UConst $eot_USort "
    "$smtx_typeof $smtx_typeof_value $smtx_value_canonical_bool "
    "$smtx_msm_lookup $emb_UOp"
)

LEAN_SINGLE_DEPS = (
    "$eot_Bool $eot_Type $eot_fun_type $eot_apply $eo_mk_apply "
    "$eo_eq $eo_ite $eo_requires $eo_and $eo_to_smt $smtx_model_eval "
    "$eo_checker_is_refutation and => $eot_UConst $eot_USort "
    "$smtx_model_eval_apply $smtx_typeof $smtx_typeof_value "
    "$smtx_value_canonical_bool $smtx_msm_lookup $emb_UOp"
)


def resolve_path_arg(path_arg: str, *, cwd: Path) -> Path:
    candidate = Path(path_arg).expanduser()
    if candidate.is_absolute():
        return candidate.resolve()
    return (cwd / candidate).resolve()


def strip_comment(line: str) -> str:
    return line.split(";", 1)[0].strip()


def input_base_name(input_file: Path) -> str:
    """The name of the calculus an input file compiles.

    This is the file name up to its first dot, so that a qualifier may be
    appended to the name of a calculus without renaming what it produces.
    """
    return input_file.name.split(".", 1)[0]


def lean_calc_name(input_file: Path) -> str:
    parts = re.findall(r"[A-Za-z0-9]+", input_base_name(input_file))
    if not parts:
        return "EoCalc"
    calc = "".join(part[:1].upper() + part[1:] for part in parts)
    if not calc[0].isalpha():
        calc = f"Calc{calc}"
    return calc


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
        defs_file: Optional[Path],
        lean_config: Optional[Path],
    ):
        self.build_dir = build_dir.resolve()
        self.final_out_dir = final_out_dir.resolve()
        self.jobs = jobs
        self.defs_file = defs_file.resolve() if defs_file else None
        self.lean_config = lean_config.resolve() if lean_config else None
        self.binary = self.build_dir / "ethos-eoc"
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
        # ethos-eoc is built by the standalone plugins/ project; configure the
        # build directory against it if this has not been done yet
        if not (self.build_dir / "CMakeCache.txt").exists():
            self.run(
                [
                    "cmake",
                    "-S",
                    str(REPO_ROOT / "plugins"),
                    "-B",
                    str(self.build_dir),
                ],
                cwd=REPO_ROOT,
            )
        self.run(
            ["cmake", "--build", ".", "--target", "ethos-eoc", f"-j{self.jobs}"]
        )

    def ethos(self, args: Iterable[str], *, quiet: bool = False) -> None:
        self.run([str(self.binary), *args], quiet=quiet)

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

    def clean_generated_lean_rule_outputs(self) -> None:
        plugin_rule_dir = self.plugin_out_dir / "lean_meta" / "rules"
        if not plugin_rule_dir.exists():
            return
        for child in plugin_rule_dir.iterdir():
            if child.is_file() and child.name.startswith("lean_meta_rule_") and child.name.endswith("_gen.lean"):
                child.unlink()

    def publish_generated_lean_rule_outputs(self, lean_dir: Path) -> None:
        """Publish the file of each rule the run compiled.

        These go under lean/Rules, which is Proofs/Rules of the package they
        are installed into with the leading component dropped, as the rest of
        the published tree is; see LEAN_OUTPUTS.
        """
        plugin_rule_dir = self.plugin_out_dir / "lean_meta" / "rules"
        final_rule_dir = lean_dir / "Rules"
        if final_rule_dir.exists():
            shutil.rmtree(final_rule_dir)
        if not plugin_rule_dir.exists():
            return
        rule_files = sorted(plugin_rule_dir.glob("lean_meta_rule_*_gen.lean"))
        if not rule_files:
            return
        final_rule_dir.mkdir(parents=True, exist_ok=True)
        for rule_file in rule_files:
            rule_name = rule_file.name[len("lean_meta_rule_") : -len("_gen.lean")]
            if not rule_name:
                continue
            module_name = rule_name[:1].upper() + rule_name[1:]
            shutil.copyfile(rule_file, final_rule_dir / f"{module_name}.lean")

    def materialize_lean_calc(self, lean_dir: Path, calc_name: str) -> None:
        for lean_file in lean_dir.rglob("*.lean"):
            replace_all(lean_file, [(LEAN_CALC_PLACEHOLDER, calc_name)])

    def stage_name(self, input_name: str) -> str:
        return input_base_name(Path(input_name)).lower()

    def trim_defs(self, input_name: str, targets: list[str], output_file: Path) -> Path:
        temp_trim = self.stage_out_dir / "temp_trim.eo"
        temp_trim.parent.mkdir(parents=True, exist_ok=True)
        pieces = [f'(include "{self.relative_input_from_out(input_name)}")\n']
        pieces.extend(self.defs_depends())
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

    def defs_blocks(self) -> list[tuple[str, str]]:
        """The blocks of the signature of the input, as (symbol, body) pairs.

        A block runs from the `; -- X` line naming the symbol it is of to the
        next such line, which is the same split the model-smt stage makes, see
        DefsFile::read in plugins/model_smt/defs_reader.cpp.
        """
        if self.defs_file is None:
            return []
        out: list[tuple[str, str]] = []
        # Prepending a newline lets the same marker recognize a block on line
        # one, which is what DefsFile::read does for the same reason. Without
        # it this side and the model-smt stage would read the same file
        # differently.
        text = "\n" + self.defs_file.read_text()
        for block in re.split(r"\n; -- ", text)[1:]:
            sym, _, body = block.partition("\n")
            out.append((sym.strip(), body))
        return out

    def defs_excludes(self) -> list[tuple[str, str]]:
        """What the signature of the input leaves out of the compilation.

        A block may say that the compilation has no place for the symbol it is
        of, as the one for lambda does: SMT-LIB gives a proof-level binder no
        meaning, so rather than a model the block gives eoc-exclude directives.
        The desugar stage is what reads those and drops what they name, see
        Desugar::echo, so they are collected here and given to it. Saying it in
        the signature is what keeps a symbol left out of the compilation from
        also having to be listed apart from it.

        Each is returned as the kind it excludes, one of rule, method or
        symbol, and the name of what it excludes.
        """
        out: list[tuple[str, str]] = []
        for _sym, body in self.defs_blocks():
            out.extend((m.group(1), m.group(2)) for m in DEFS_EXCLUDE.finditer(body))
        return out

    def defs_excluded_rules(self) -> set[str]:
        """Those of the exclusions that are proof rules.

        The compilation has nothing to say about such a rule: no verification
        condition to generate and no Lean file to write. So a run over every
        rule of the input leaves it out, and a run that names it says why
        rather than failing further down.
        """
        return {name for kind, name in self.defs_excludes() if kind == "rule"}

    def defs_depends(self) -> list[str]:
        """What trim-defs must keep for the model of each symbol to make sense.

        A block of the signature of the input may name a symbol of that input,
        as the transformation of @quantifiers_skolemize names forall in the
        pattern it matches. Trimming the input to one proof rule has to keep
        such a symbol, or the case the model-smt stage emits for the block
        would name something the trimmed signature no longer declares. The
        dependency is read off the block itself, so nothing states it twice.

        A symbol of the input is a name in head position that no program of the
        block binds and that is neither of the embedding, which is written with
        a leading dollar, nor of Eunoia, which is written eo::.
        """
        out: list[str] = []
        for sym, body in self.defs_blocks():
            body = DEFS_DIRECTIVE.sub("", body)
            body = re.sub(r";[^\n]*", "", body)
            bound = {sym, "program", "define", "declare-const",
                     "declare-parameterized-const"}
            for params in re.findall(r"\(\((?:[^()]|\([^()]*\))*\)\)", body):
                bound.update(re.findall(r"\(([^\s()]+)", params))
            heads = set(re.findall(r"\(([A-Za-z@_][^\s()]*)", body))
            names = {h for h in heads - bound if not h.startswith("eo::")}
            if names:
                out.append('(echo "trim-defs-cmd (depends %s %s)")\n'
                           % (sym, " ".join(sorted(names))))
        return out

    def desugar(
        self,
        input_name: str,
        output_file: Path,
        *,
        deps: Optional[str],
        plugin_label: Optional[str],
    ) -> Path:
        args = ["--plugin.desugar"]
        # What the signature of the input leaves out of the compilation, which
        # this stage is what applies, see defs_excludes.
        excludes = self.defs_excludes()
        temp_excludes = self.stage_out_dir / "temp_excludes.eo"
        if excludes:
            temp_excludes.parent.mkdir(parents=True, exist_ok=True)
            temp_excludes.write_text(
                "".join('(echo "eoc-exclude %s %s")\n' % e for e in excludes)
            )
            args.append(f"--include={self.binary_path_arg(temp_excludes)}")
        args.append(input_name)
        try:
            self.ethos(args, quiet=True)
        finally:
            if excludes and temp_excludes.exists():
                temp_excludes.unlink()
        output_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(self.plugin_generated("desugar/eo_desugar_gen.eo"), output_file)
        replacements: list[tuple[str, str]] = []
        if deps is not None:
            replacements.append(("eo-desugar-deps", deps))
        if plugin_label is not None:
            replacements.append(("eo-desugar", plugin_label))
        if replacements:
            replace_all(output_file, replacements)
        inline_include(
            output_file,
            "eo_desugar_native.eo",
            self.plugin_generated("desugar/eo_desugar_native.eo"),
        )
        inline_include(
            output_file,
            "native_embed.eo",
            self.plugin_generated("desugar/native_embed.eo"),
        )
        return output_file

    def model_smt(self, input_file: Path, output_file: Path) -> Path:
        # The signature of the input written in the deep embedding, which says
        # what its symbols mean to the model. This stage alone reads it, so it
        # is named here rather than being part of the input; see the
        # "signatures written in the deep embedding" section of
        # tools/eoc/README.md.
        args = ["--plugin.model-smt"]
        if self.defs_file is not None:
            args.append(f"--defs={self.binary_path_arg(self.defs_file)}")
        args.append(self.binary_path_arg(input_file))
        self.ethos(args, quiet=True)
        output_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(input_file, output_file)
        splice_matching_line(
            output_file,
            'include model_smt',
            self.plugin_generated("model_smt/model_smt_gen.eo"),
        )
        return output_file

    def lean(
        self,
        input_file: Path,
        *,
        calc_name: str,
        generate_parser: bool,
    ) -> Path:
        out_lean = self.final_out_dir / "lean"
        out_lean.mkdir(parents=True, exist_ok=True)
        self.clean_generated_lean_rule_outputs()
        parser_outputs = (
            self.plugin_generated("lean_meta/lean_meta_parser_gen.lean"),
            out_lean / "Parser.lean",
        )
        if not generate_parser:
            for parser_output in parser_outputs:
                if parser_output.exists():
                    parser_output.unlink()
        args = ["--plugin.lean-meta"]
        if not generate_parser:
            args.append("--no-parser")
        # What the input signature needs said about its generated Lean that the
        # compiler cannot derive, namely why each of its recursive programs
        # terminates; see plugins/lean_meta/termination.lean.
        if self.lean_config is not None:
            args.append(f"--lean-config={self.binary_path_arg(self.lean_config)}")
        args.append(self.binary_path_arg(input_file))
        self.ethos(args, quiet=True)
        for source, name, generated in LEAN_OUTPUTS:
            if not generate_parser and name == "Parser.lean":
                continue
            source_path = (
                self.plugin_generated(source)
                if generated
                else REPO_ROOT / "plugins" / source
            )
            shutil.copyfile(source_path, out_lean / name)
        self.publish_generated_lean_rule_outputs(out_lean)
        self.materialize_lean_calc(out_lean, calc_name)
        return out_lean

    def parse_file(self, filename: Path) -> None:
        self.ethos([self.binary_path_arg(filename)], quiet=True)

    def run_lean(
        self,
        input_name: str,
        targets: list[str],
        *,
        all_targets: bool,
        build_first: bool,
        generate_parser: bool,
    ) -> Path:
        if build_first:
            self.build()
        left_out = sorted(set(targets) & self.defs_excluded_rules())
        if left_out:
            raise RuntimeError(
                f"{' '.join(left_out)} is left out of the compilation by "
                f"{self.defs_file}, so there is no Lean to generate for it"
            )
        calc_name = lean_calc_name(Path(input_name))
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
                deps=LEAN_ALL_DEPS,
                plugin_label="lean-meta",
            )
            print(f"**** lean_meta: Run ethos + model-smt on {init_desugar} to generate {final_defs}")
            self.model_smt(init_desugar, final_defs)
            print(f"**** lean_meta: Verify ethos parses {final_defs}")
            self.parse_file(final_defs)
            print(f"**** lean_meta: Generate Lean from {final_defs} to {self.final_out_dir / 'lean'}")
            return self.lean(
                final_defs,
                calc_name=calc_name,
                generate_parser=generate_parser,
            )

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
            deps=LEAN_SINGLE_DEPS,
            plugin_label="lean-meta",
        )
        print(f"**** lean_meta: Run ethos + model-smt on {init_desugar} to generate {vcm_defs}")
        self.model_smt(init_desugar, vcm_defs)
        # The generated proof parser expands parameterized n-ary syntax with
        # the calculus' own nil/type utilities. Keep those utilities even when
        # compiling only a small set of rules; parser metadata echoes are
        # intentionally preserved by trim-defs as well.
        target_progs = [f"$eo_prog_{target}" for target in targets]
        target_progs.extend(["$eo_nil", "$eo_typeof"])
        print(f"**** lean_meta: Run ethos + trim-deps on {vcm_defs} to generate {final_defs}")
        self.trim_defs(self.binary_path_arg(vcm_defs), target_progs, final_defs)
        print(f"**** lean_meta: Verify ethos parses {final_defs}")
        self.parse_file(final_defs)
        print(f"**** lean_meta: Generate Lean from {final_defs} to {self.final_out_dir / 'lean'}")
        return self.lean(
            final_defs,
            calc_name=calc_name,
            generate_parser=generate_parser,
        )

    def run_desugar(self, input_name: str, *, build_first: bool) -> Path:
        if build_first:
            self.build()
        output = self.final_out_dir / "desugar.eo"
        print(f"**** desugar: Run ethos + desugar on {input_name} to generate {output}")
        self.desugar(input_name, output, deps=None, plugin_label=None)
        print("**** desugar: Verify it parses")
        self.parse_file(output)
        return output

    def run_trim_only(self, input_name: str, targets: list[str], *, build_first: bool) -> Path:
        if build_first:
            self.build()
        output = self.final_out_dir / "trim_defs" / "trim_gen.eo"
        print(f"**** run_trim_defs: Run ethos + trim-defs on {input_name}")
        self.trim_defs(input_name, targets, output)
        return output

def add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--build-dir",
        default=os.getcwd(),
        help="Build directory for the plugins/ project, containing ethos-eoc and out/.",
    )
    parser.add_argument(
        "--final-out-dir",
        default=None,
        help="Directory for final published outputs. Defaults to $EOC_FINAL_OUT_DIR or tools/eoc/out.",
    )
    parser.add_argument("--jobs", type=int, default=4, help="Parallel build jobs.")
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Do not rebuild ethos-eoc before running the pipeline.",
    )
    parser.add_argument(
        "--defs",
        default=None,
        help=(
            "EO file of the signature of the input written in the deep "
            "embedding, read by the model-smt stage. Defaults to "
            "plugins/model_smt/cpc_defs.eo."
        ),
    )
    parser.add_argument(
        "--lean-config",
        default=None,
        help=(
            "Lean file of the termination clauses of the input's programs, "
            "read by the lean-meta stage."
        ),
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    lean = subparsers.add_parser("lean", help="Generate Lean output for selected rules.")
    add_common_args(lean)
    lean.add_argument("input")
    lean.add_argument("targets", nargs="*")
    lean.add_argument("--all", action="store_true", help="Compile the entire signature.")
    lean.add_argument(
        "--no-parser",
        action="store_true",
        help="Do not generate or publish the signature-specific Logos parser.",
    )

    desugar = subparsers.add_parser("desugar", help="Generate a desugared EO file.")
    add_common_args(desugar)
    desugar.add_argument("input")

    trim = subparsers.add_parser("trim-defs", help="Run the trim-defs plugin only.")
    add_common_args(trim)
    trim.add_argument("input")
    trim.add_argument("targets", nargs="+")

    list_rules = subparsers.add_parser(
        "list-rules", help="Print declared rules from a signature and its includes."
    )
    list_rules.add_argument("input")

    args = parser.parse_args(argv)
    invocation_cwd = Path.cwd().resolve()

    if hasattr(args, "input"):
        args.input = str(resolve_path_arg(args.input, cwd=invocation_cwd))

    if getattr(args, "final_out_dir", None) is not None:
        final_out_dir = resolve_path_arg(args.final_out_dir, cwd=invocation_cwd)
    else:
        final_out_env = os.environ.get("EOC_FINAL_OUT_DIR")
        if final_out_env:
            final_out_dir = resolve_path_arg(final_out_env, cwd=invocation_cwd)
        else:
            final_out_dir = DEFAULT_FINAL_OUT_DIR

    def resolve_file_arg(name: str, flag: str) -> Optional[Path]:
        """The file the given option names, resolved as the input is.

        It has to exist: read as empty, a mistyped --defs would quietly
        compile a signature with no exclusions and no dependencies instead of
        saying that the file it was pointed at is not there.
        """
        value = getattr(args, name, None)
        if value is None:
            return None
        resolved = resolve_path_arg(value, cwd=invocation_cwd)
        if not resolved.is_file():
            parser.error(f"{flag} file not found: {resolved}")
        return resolved

    build_dir_arg = getattr(args, "build_dir", None) or os.getcwd()
    pipeline = Pipeline(
        resolve_path_arg(build_dir_arg, cwd=invocation_cwd),
        final_out_dir,
        getattr(args, "jobs", 4),
        resolve_file_arg("defs", "--defs"),
        resolve_file_arg("lean_config", "--lean-config"),
    )
    build_first = not getattr(args, "no_build", False)
    if not build_first and not pipeline.binary.is_file():
        parser.error(
            f"ethos-eoc not found at {pipeline.binary}; drop --no-build or "
            "name the build directory it is in with --build-dir"
        )

    try:
        if args.command == "lean":
            if not args.all and not args.targets:
                parser.error("lean requires at least one target unless --all is passed")
            if args.all and args.targets:
                parser.error(
                    "lean --all compiles the whole signature; it takes no targets, "
                    f"but was given {' '.join(args.targets)}"
                )
            pipeline.run_lean(
                args.input,
                list(args.targets),
                all_targets=args.all,
                build_first=build_first,
                generate_parser=not args.no_parser,
            )
        elif args.command == "desugar":
            pipeline.run_desugar(args.input, build_first=build_first)
        elif args.command == "trim-defs":
            pipeline.run_trim_only(
                args.input,
                list(args.targets),
                build_first=build_first,
            )
        else:
            for rule in discover_rules(Path(args.input)):
                print(rule)
        return 0
    except subprocess.CalledProcessError as err:
        return err.returncode
    except RuntimeError as err:
        print(err, file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
