#!/usr/bin/env bash
# Shared helper library for the CPC wrappers in this directory.
# Source this file from the wrapper scripts; it is not meant to be run directly.
# The wrappers default to publishing stage and final artifacts in tools/eoc/out.
# shellcheck shell=bash

# How a script says what it is doing, which is how the tools it calls say it
# too, see tools/eoc/report.py: a step of a run is a line under `-- ', what a
# step is made of is indented two spaces further under it, and a path is
# written from the root of the repository. What went wrong is not a step: it
# goes to stderr as `error: ...', where the CI of a caller looks for it.
eoc_step() { printf -- '-- %s\n' "$*"; }
eoc_item() { printf -- '--   %s\n' "$*"; }
eoc_error() { printf 'error: %s\n' "$*" >&2; }
eoc_warning() { printf 'warning: %s\n' "$*" >&2; }

# A path as a log names one: from the root of the repository where it is under
# it, and as it stands otherwise, e.g. a tree the signature is read from.
eoc_rel() {
  case "$1" in
    "$EOC_REPO_ROOT"/*) printf '%s\n' "${1#"$EOC_REPO_ROOT"/}" ;;
    *) printf '%s\n' "$1" ;;
  esac
}

EOC_COMPAT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EOC_TOOLS_DIR="$(cd "$EOC_COMPAT_DIR/.." && pwd)"
EOC_REPO_ROOT="$(cd "$EOC_COMPAT_DIR/../../.." && pwd)"
EOC_DRIVER="$EOC_TOOLS_DIR/driver.py"
# The input is the CPC signature itself. What its symbols mean to the model is
# said by a signature of its own, written in the deep embedding, which the
# model-smt stage is given with --signature.
#
# What is named here is the *configuration* of that signature rather than the
# signature itself: the driver compiles it before the model-smt stage and gives
# the stage what it compiled to, so the two are never out of step. See
# compile_signatures in tools/eoc/driver.py.
EOC_DEFAULT_CPC_INPUT="$EOC_REPO_ROOT/../cvc5-ajr/proofs/eo/cpc/Cpc.eo"
EOC_DEFAULT_CPC_SIGNATURE="$EOC_TOOLS_DIR/semantics/development-cpc.eos"
# The SMT-LIB semantics it is written against, which is the target of the
# compilation and so the same whichever input a run compiles.
EOC_DEFAULT_SEMANTICS="$EOC_TOOLS_DIR/semantics/smt.eos"
# Why each of its recursive programs terminates, which the generated Lean has
# to say and the compiler cannot derive. This is what the configuration named
# above compiles it to, which the driver gives the lean-meta stage of itself,
# so nothing here passes --lean-config unless the caller named another; see
# compile_signatures in tools/eoc/driver.py.
EOC_DEFAULT_CPC_LEAN_CONFIG="$EOC_TOOLS_DIR/out/user_termination.lean"
EOC_DEFAULT_FINAL_OUT_DIR="$EOC_TOOLS_DIR/out"

eoc_default_build_dir() {
  if [[ -x "$PWD/ethos-eoc" ]]; then
    printf '%s\n' "$PWD"
    return
  fi
  printf '%s\n' "$EOC_REPO_ROOT/build-eoc"
}

eoc_build_dir() {
  printf '%s\n' "${BUILD_DIR:-$(eoc_default_build_dir)}"
}

eoc_cpc_input() {
  printf '%s\n' "${EOC_CPC_INPUT:-$EOC_DEFAULT_CPC_INPUT}"
}

eoc_cpc_signature() {
  printf '%s\n' "${EOC_CPC_SIGNATURE:-$EOC_DEFAULT_CPC_SIGNATURE}"
}

# Append the signature of the input to ARGS. An input given by the caller has a
# signature of its own or none at all, so the default is used only for the
# default input.
eoc_add_signature() {
  if [[ -n "${EOC_CPC_SIGNATURE:-}" ]]; then
    ARGS+=("--signature=${EOC_CPC_SIGNATURE}")
  elif [[ -z "${EOC_CPC_INPUT:-}" ]]; then
    ARGS+=("--signature=$EOC_DEFAULT_CPC_SIGNATURE")
  fi
}

# The SMT-LIB semantics the signature of an input is written against, which
# every input is compiled through. It is the target of the compilation, so a
# run leaves it to the one the model-smt stage ships with unless it names
# another; naming one is what says the semantics are a configuration too.
eoc_semantics() {
  printf '%s\n' "${EOC_SEMANTICS:-$EOC_DEFAULT_SEMANTICS}"
}

eoc_add_semantics() {
  if [[ -n "${EOC_SEMANTICS:-}" ]]; then
    ARGS+=("--semantics=${EOC_SEMANTICS}")
  fi
}

eoc_cpc_lean_config() {
  printf '%s\n' "${EOC_CPC_LEAN_CONFIG:-$EOC_DEFAULT_CPC_LEAN_CONFIG}"
}

# Append the Lean configuration of the input to ARGS. The clauses of a
# signature given as a configuration are compiled with it, and the driver reads
# them from where that set compiled them, so this names one only where the
# caller did: naming the default here would be right only for a set of this
# tree, since any other compiles beside itself.
eoc_add_lean_config() {
  if [[ -n "${EOC_CPC_LEAN_CONFIG:-}" ]]; then
    ARGS+=("--lean-config=${EOC_CPC_LEAN_CONFIG}")
  fi
}

eoc_final_out_dir() {
  printf '%s\n' "${EOC_FINAL_OUT_DIR:-$EOC_DEFAULT_FINAL_OUT_DIR}"
}

eoc_add_no_build() {
  if [[ "${EOC_NO_BUILD:-0}" != "0" ]]; then
    ARGS+=(--no-build)
  fi
}

eoc_add_skip_cvc5() {
  if [[ "${EOC_SKIP_CVC5:-0}" != "0" ]]; then
    ARGS+=(--skip-cvc5)
  fi
}

eoc_extract_solve_options() {
  local saw_solve=0
  local saw_solve_args=0
  local need_solve_args_value=0
  local solve_args_value=""
  local arg
  EOC_FILTERED_ARGS=()
  for arg in "$@"; do
    if (( need_solve_args_value )); then
      solve_args_value="$arg"
      saw_solve_args=1
      need_solve_args_value=0
      continue
    fi
    case "$arg" in
      --solve)
        saw_solve=1
        ;;
      --solve-args)
        need_solve_args_value=1
        ;;
      --solve-args=*)
        solve_args_value="${arg#--solve-args=}"
        saw_solve_args=1
        ;;
      *)
        EOC_FILTERED_ARGS+=("$arg")
        ;;
    esac
  done
  if (( need_solve_args_value )); then
    eoc_error "--solve-args requires a value"
    exit 2
  fi
  if (( saw_solve )); then
    ARGS+=(--solve)
  fi
  if (( saw_solve_args )); then
    ARGS+=("--solve-args=$solve_args_value")
  fi
}

eoc_require_args() {
  local usage="$1"
  local expected="$2"
  local actual="$3"
  if (( actual < expected )); then
    echo "usage: $usage" >&2
    exit 2
  fi
}

eoc_exec_driver() {
  exec python3 "$EOC_DRIVER" "$@"
}

eoc_lean_calc_name() {
  local input_path="$1"
  local stem
  local normalized
  local calc=""
  local part

  # The name of the calculus is the file name up to its first dot.
  # Keep this in sync with input_base_name in tools/eoc/driver.py.
  stem="$(basename "$input_path")"
  stem="${stem%%.*}"
  normalized="$(printf '%s' "$stem" | tr -cs '[:alnum:]' ' ')"
  for part in $normalized; do
    calc+="${part^}"
  done
  if [[ -z "$calc" ]]; then
    calc="EoCalc"
  fi
  if [[ ! "$calc" =~ ^[[:alpha:]] ]]; then
    calc="Calc$calc"
  fi
  printf '%s\n' "$calc"
}

eoc_detect_generated_lean_calc() {
  local final_out_dir="$1"
  local logos_file="$final_out_dir/lean/Logos.lean"
  local import_line

  if [[ ! -f "$logos_file" ]]; then
    return 1
  fi
  import_line="$(grep -m1 '^import ' "$logos_file" || true)"
  # Allow an optional `all` modifier (Lean's `import all Foo`) before the module
  # name so the calc name is detected without swallowing the modifier.
  if [[ "$import_line" =~ ^import[[:space:]]+(all[[:space:]]+)?([^.]+)\. ]]; then
    printf '%s\n' "${BASH_REMATCH[2]}"
    return 0
  fi
  return 1
}

eoc_sed_in_place() {
  local expression="$1"
  local file="$2"
  sed -i.bak -e "$expression" "$file"
  rm -f "$file.bak"
}

eoc_rewrite_lean_calc_imports() {
  local dest_dir="$1"
  local src_calc="$2"
  local dst_calc="$3"
  local file

  if [[ "$src_calc" == "$dst_calc" ]]; then
    return
  fi
  while IFS= read -r -d '' file; do
    # Preserve an optional `all` modifier (captured as \1) when rewriting the
    # calc namespace so `import all ${src_calc}.` stays `import all ${dst_calc}.`.
    eoc_sed_in_place \
      "s/import \\(all \\)\\{0,1\\}${src_calc}\\./import \\1${dst_calc}\\./g" \
      "$file"
  done < <(find "$dest_dir" -type f -name '*.lean' -print0)
}

# Compile the configuration of the model-smt signatures, and say what came out.
#
# The stage reads two signatures written in the deep embedding: the SMT-LIB one,
# smt_defs.eo, which it finds for itself since it is the target, and the input's,
# user_defs.eo, which --signature names. Both are generated from the
# configuration under tools/eoc/semantics. The driver compiles them before any
# stage runs (see compile_signatures in tools/eoc/driver.py) but does so
# silently, so a run never says where user_defs.eo came from; this compiles them
# first, where the compiler says it. Doing so costs nothing and leaves the
# driver's own pass with nothing to do: a file is written only where its text
# changed.
#
# Which sets are compiled is sem_compile's own business rather than something
# listed here, so the two cannot drift. One named with EOC_CPC_SIGNATURE that is
# not among the sets the tool ships with is compiled by the driver during the
# run rather than reported here.
eoc_compile_sem_signatures() {
  python3 "$EOC_TOOLS_DIR/sem_compile.py"
}

# The signature-wide Lean files installed by eoc_copy_lean_outputs, in module
# dependency order. Each entry is "<source under out/lean> <destination
# relative to the installed package directory>". This list must cover every
# file written by the lean subcommand of tools/eoc/driver.py apart from the
# per-rule files under out/lean/Rules/, which eoc_copy_lean_outputs installs
# into Proofs/Rules/; a file added there but not here is silently left behind.
EOC_LEAN_OUTPUTS=(
  "Logos.lean Logos.lean"
  "LogosTerm.lean LogosTerm.lean"
  "Parser.lean Parser.lean"
  "SmtEval.lean SmtEval.lean"
  "SmtModelDefs.lean SmtModelDefs.lean"
  "SmtValueOrder.lean SmtValueOrder.lean"
  "SmtModel.lean SmtModel.lean"
  "Spec.lean Spec.lean"
  "RuleLemmas.lean Proofs/RuleLemmas.lean"
)

eoc_copy_lean_outputs() {
  local dest_dir="$1"
  local final_out_dir="$2"
  local preserve_existing_rules="${3:-0}"
  local include_parser="${4:-1}"
  local lean_dir="$final_out_dir/lean"
  local rules_dir="$lean_dir/Rules"
  local entry
  local src
  local dest
  local file
  local rule_dest
  local copied
  local preserved
  local at

  mkdir -p "$dest_dir" "$dest_dir/Proofs" "$dest_dir/Proofs/Rules"
  eoc_step "Installing the generated Lean of $(eoc_rel "$lean_dir") into $(eoc_rel "$dest_dir")"
  # What each line names the file it copied by, padded so that the files line
  # up under one another.
  at=0
  for entry in "${EOC_LEAN_OUTPUTS[@]}"; do
    read -r src dest <<< "$entry"
    [[ "${#src}" -gt "$at" ]] && at="${#src}"
  done
  for entry in "${EOC_LEAN_OUTPUTS[@]}"; do
    read -r src dest <<< "$entry"
    if [[ "$include_parser" == "0" && "$src" == "Parser.lean" ]]; then
      rm -f "$dest_dir/$dest"
      continue
    fi
    if [[ ! -f "$lean_dir/$src" ]]; then
      eoc_error "$(eoc_rel "$lean_dir/$src") was not generated"
      return 1
    fi
    eoc_item "$(printf '%-*s -> %s' "$at" "$src" "$(basename "$dest_dir")/$dest")"
    cp "$lean_dir/$src" "$dest_dir/$dest"
  done
  if [[ -d "$rules_dir" ]]; then
    (
      shopt -s nullglob
      copied=0
      preserved=0
      for file in "$rules_dir"/*.lean; do
        rule_dest="$dest_dir/Proofs/Rules/$(basename "$file")"
        if [[ "$preserve_existing_rules" != "0" && -e "$rule_dest" ]]; then
          preserved=$((preserved + 1))
          continue
        fi
        cp "$file" "$rule_dest"
        copied=$((copied + 1))
      done
      eoc_item "$(printf '%-*s -> %s (%s)' "$at" "Rules/*.lean" \
        "$(basename "$dest_dir")/Proofs/Rules/" \
        "$copied copied, $preserved preserved")"
    )
  fi
}
