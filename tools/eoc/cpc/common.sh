#!/usr/bin/env bash
# Shared helper library for the CPC compatibility wrappers in this directory.
# Source this file from the wrapper scripts; it is not meant to be run directly.
# The wrappers default to publishing stage and final artifacts in tools/eoc/out.
# shellcheck shell=bash

EOC_COMPAT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EOC_TOOLS_DIR="$(cd "$EOC_COMPAT_DIR/.." && pwd)"
EOC_REPO_ROOT="$(cd "$EOC_COMPAT_DIR/../../.." && pwd)"
EOC_DRIVER="$EOC_TOOLS_DIR/driver.py"
# The input is the CPC signature itself. What its symbols mean to the model is
# said by a signature of its own, written in the deep embedding, which the
# model-smt stage is given with --defs.
EOC_DEFAULT_CPC_INPUT="$EOC_REPO_ROOT/../cvc5-ajr/proofs/eo/cpc/Cpc.eo"
EOC_DEFAULT_CPC_DEFS="$EOC_REPO_ROOT/plugins/model_smt/cpc_defs.eo"
# Why each of its recursive programs terminates, which the generated Lean has
# to say and the compiler cannot derive; given to the lean-meta stage with
# --lean-config.
EOC_DEFAULT_CPC_LEAN_CONFIG="$EOC_REPO_ROOT/plugins/lean_meta/cpc_termination.lean"
EOC_DEFAULT_ALETHE_INPUT="$EOC_REPO_ROOT/../AletheInEunoia/signature/Alethe.eo"
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

eoc_cpc_defs() {
  printf '%s\n' "${EOC_CPC_DEFS:-$EOC_DEFAULT_CPC_DEFS}"
}

# Append the signature of the input to ARGS. An input given by the caller has a
# signature of its own or none at all, so the default is used only for the
# default input.
eoc_add_defs() {
  if [[ -n "${EOC_CPC_DEFS:-}" ]]; then
    ARGS+=("--defs=${EOC_CPC_DEFS}")
  elif [[ -z "${EOC_CPC_INPUT:-}" ]]; then
    ARGS+=("--defs=$EOC_DEFAULT_CPC_DEFS")
  fi
}

eoc_cpc_lean_config() {
  printf '%s\n' "${EOC_CPC_LEAN_CONFIG:-$EOC_DEFAULT_CPC_LEAN_CONFIG}"
}

# Append the Lean configuration of the input to ARGS, on the same terms as
# eoc_add_defs: an input given by the caller has one of its own or none at all.
eoc_add_lean_config() {
  if [[ -n "${EOC_CPC_LEAN_CONFIG:-}" ]]; then
    ARGS+=("--lean-config=${EOC_CPC_LEAN_CONFIG}")
  elif [[ -z "${EOC_CPC_INPUT:-}" ]]; then
    ARGS+=("--lean-config=$EOC_DEFAULT_CPC_LEAN_CONFIG")
  fi
}

eoc_alethe_input() {
  printf '%s\n' "${EOC_ALETHE_INPUT:-$EOC_DEFAULT_ALETHE_INPUT}"
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
    echo "error: --solve-args requires a value" >&2
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

eoc_run_driver() {
  python3 "$EOC_DRIVER" "$@"
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

  mkdir -p "$dest_dir" "$dest_dir/Proofs" "$dest_dir/Proofs/Rules"
  echo "Installing generated Lean files from $lean_dir into $dest_dir"
  for entry in "${EOC_LEAN_OUTPUTS[@]}"; do
    read -r src dest <<< "$entry"
    if [[ "$include_parser" == "0" && "$src" == "Parser.lean" ]]; then
      rm -f "$dest_dir/$dest"
      continue
    fi
    if [[ ! -f "$lean_dir/$src" ]]; then
      echo "error: $lean_dir/$src was not generated" >&2
      return 1
    fi
    echo "  $src -> $dest_dir/$dest"
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
      echo "  Rules/*.lean -> $dest_dir/Proofs/Rules/" \
        "($copied copied, $preserved existing preserved)"
    )
  fi
}
