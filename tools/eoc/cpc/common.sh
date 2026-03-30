#!/usr/bin/env bash
# shellcheck shell=bash

EOC_COMPAT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EOC_TOOLS_DIR="$(cd "$EOC_COMPAT_DIR/.." && pwd)"
EOC_REPO_ROOT="$(cd "$EOC_COMPAT_DIR/../../.." && pwd)"
EOC_DRIVER="$EOC_TOOLS_DIR/driver.py"
EOC_DEFAULT_CPC_INPUT="$EOC_REPO_ROOT/../cvc5-ajr/proofs/eo/cpc/Cpc.eo"
EOC_DEFAULT_ALETHE_INPUT="$EOC_REPO_ROOT/../AletheInEunoia/signature/Alethe.eo"

eoc_default_build_dir() {
  if [[ -x "$PWD/src/ethos-eoc" ]]; then
    printf '%s\n' "$PWD"
    return
  fi
  printf '%s\n' "$EOC_REPO_ROOT/build"
}

eoc_build_dir() {
  printf '%s\n' "${BUILD_DIR:-$(eoc_default_build_dir)}"
}

eoc_cpc_input() {
  printf '%s\n' "${EOC_CPC_INPUT:-$EOC_DEFAULT_CPC_INPUT}"
}

eoc_alethe_input() {
  printf '%s\n' "${EOC_ALETHE_INPUT:-$EOC_DEFAULT_ALETHE_INPUT}"
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

eoc_copy_lean_outputs() {
  local dest_dir="$1"
  local build_dir="$2"
  local lean_dir="$build_dir/out/lean"

  mkdir -p "$dest_dir"
  cp "$lean_dir/Logos.lean" "$dest_dir/Logos.lean"
  cp "$lean_dir/SmtEval.lean" "$dest_dir/SmtEval.lean"
  cp "$lean_dir/SmtModel.lean" "$dest_dir/SmtModel.lean"
  cp "$lean_dir/Spec.lean" "$dest_dir/Spec.lean"
  cp "$lean_dir/Lemmas.lean" "$dest_dir/Lemmas.lean"
}
