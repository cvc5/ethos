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
# model-smt stage is given with --semantics.
#
# What is named here is the *configuration* of those semantics rather than the
# signature itself: the driver compiles it before the model-smt stage and gives
# the stage what it compiled to, so the two are never out of step. See
# compile_signatures in tools/eoc/driver.py.
EOC_DEFAULT_CPC_INPUT="$EOC_REPO_ROOT/../cvc5-ajr/proofs/eo/cpc/Cpc.eo"
EOC_DEFAULT_SEMANTICS="$EOC_TOOLS_DIR/semantics/development-cpc.eos"
# Two more a run needs are named nowhere here, since nothing here would be the
# one to say them: the SMT-LIB semantics the above is written against is the
# target of the compilation, which sem_compile.py holds the set of, and why
# each of the input's recursive programs terminates is what that same
# compilation writes and the driver gives the lean-meta stage of itself. A
# caller that has another of either says so with EOC_SMT_SEMANTICS or
# EOC_CPC_LEAN_CONFIG; see compile_signatures in tools/eoc/driver.py.
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

# Append the semantics of the input to ARGS. An input given by the caller has
# semantics of its own or none at all, so the default is used only for the
# default input.
eoc_add_semantics() {
  if [[ -n "${EOC_SEMANTICS:-}" ]]; then
    ARGS+=("--semantics=${EOC_SEMANTICS}")
  elif [[ -z "${EOC_CPC_INPUT:-}" ]]; then
    ARGS+=("--semantics=$EOC_DEFAULT_SEMANTICS")
  fi
}

# The SMT-LIB semantics the semantics of an input are written against, which
# every input is compiled through. It is the target of the compilation, so a
# run leaves it to the one the tool ships with unless it names another; naming
# one is what says those semantics are a configuration too.
eoc_add_smt_semantics() {
  if [[ -n "${EOC_SMT_SEMANTICS:-}" ]]; then
    ARGS+=("--smt-semantics=${EOC_SMT_SEMANTICS}")
  fi
}

# Append the Lean configuration of the input to ARGS. The clauses of semantics
# given as a configuration are compiled with them, and the driver gives the
# stage what that set compiled to, so this names one only where the caller
# did -- which is for a signature given already written out.
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

# Append the name the generated Lean is to call the calculus, which is the name
# of the package it is installed into. A caller that installs says which; a run
# that names none leaves the driver to call it after the input.
eoc_add_calc_name() {
  if [[ -n "${EOC_LEAN_CALC:-}" ]]; then
    ARGS+=("--calc-name=${EOC_LEAN_CALC}")
  fi
}

eoc_sed_in_place() {
  local expression="$1"
  local file="$2"
  sed -i.bak -e "$expression" "$file"
  rm -f "$file.bak"
}

# Compile the configuration of the model-smt signatures, and say what came out.
#
# The stage reads two signatures written in the deep embedding: the SMT-LIB one,
# smt_defs.eo, which it finds for itself since it is the target, and the input's,
# user_defs.eo, which --semantics names. Both are generated from the
# configuration under tools/eoc/semantics. The driver compiles them before any
# stage runs (see compile_signatures in tools/eoc/driver.py) but does so
# silently, so a run never says where user_defs.eo came from; this compiles them
# first, where the compiler says it. Doing so costs nothing and leaves the
# driver's own pass with nothing to do: a file is written only where its text
# changed.
#
# Which sets are compiled is sem_compile's own business rather than something
# listed here, so the two cannot drift. One named with EOC_SEMANTICS that is
# not among the sets the tool ships with is compiled by the driver during the
# run rather than reported here.
eoc_compile_sem_signatures() {
  python3 "$EOC_TOOLS_DIR/sem_compile.py"
}

# Install the generated Lean into a package.
#
# The driver publishes the tree in the layout of the package it is installed
# into, see LEAN_OUTPUTS in tools/eoc/driver.py, so this copies the tree as it
# stands and no list here says what is in it: a file added there arrives with
# no change on this side. What the run did not generate is what the package is
# not to keep, so a Parser.lean of an earlier run goes where this one wrote
# none.
#
# A rule file already in the package is kept where the caller says so, since a
# hand-written proof may stand beside the generated one.
eoc_copy_lean_outputs() {
  local dest_dir="$1"
  local final_out_dir="$2"
  local preserve_existing_rules="${3:-0}"
  local lean_dir="$final_out_dir/lean"
  local file
  local rel
  local dest
  local copied=0
  local preserved=0

  if [[ ! -f "$lean_dir/Logos.lean" ]]; then
    eoc_error "$(eoc_rel "$lean_dir") holds no generated Lean"
    return 1
  fi
  eoc_step "Installing the generated Lean of $(eoc_rel "$lean_dir") into $(eoc_rel "$dest_dir")"
  [[ -f "$lean_dir/Parser.lean" ]] || rm -f "$dest_dir/Parser.lean"
  while IFS= read -r -d '' file; do
    rel="${file#"$lean_dir"/}"
    dest="$dest_dir/$rel"
    if [[ "$preserve_existing_rules" != "0" && "$rel" == Proofs/Rules/* \
          && -e "$dest" ]]; then
      preserved=$((preserved + 1))
      continue
    fi
    mkdir -p "$(dirname "$dest")"
    cp "$file" "$dest"
    copied=$((copied + 1))
  done < <(find "$lean_dir" -type f -name '*.lean' -print0)
  eoc_item "$(printf '%d copied, %d preserved' "$copied" "$preserved")"
}
