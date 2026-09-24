#!/usr/bin/env bash

set -euo pipefail

usage()
{
  echo "Usage: $0 SIGNATURE.eo [OUTPUT_DIR] [release|debug]"
  echo
  echo "Build a generator, compile SIGNATURE.eo to C++, and build a custom"
  echo "ethos binary whose executor auto-loads that generated signature."
}

if [[ $# -lt 1 || $# -gt 3 || "$1" == "-h" || "$1" == "--help" ]]; then
  usage
  if [[ $# -ge 1 && ( "$1" == "-h" || "$1" == "--help" ) ]]; then
    exit 0
  fi
  exit 2
fi

signature_input=$1
if [[ ! -f "$signature_input" ]]; then
  echo "error: signature does not exist: $signature_input" >&2
  exit 2
fi
case "$signature_input" in
  *.eo) ;;
  *)
    echo "error: signatures must have the .eo extension: $signature_input" >&2
    exit 2
    ;;
esac

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
repo_root=$(cd "$script_dir/../.." && pwd -P)
signature_dir=$(cd "$(dirname "$signature_input")" && pwd -P)
signature_path="$signature_dir/$(basename "$signature_input")"

output_input=${2:-"$repo_root/build/cpp_compiler_custom"}
mkdir -p "$output_input"
output_dir=$(cd "$output_input" && pwd -P)

case ${3:-release} in
  release) build_type=Release ;;
  debug) build_type=Debug ;;
  *)
    echo "error: build type must be release or debug" >&2
    exit 2
    ;;
esac

generator_build="$output_dir/generator-build"
executor_build="$output_dir/executor-build"
generated_source="$output_dir/compiled.out.cpp"

echo "[1/3] Building the signature compiler"
cmake -S "$script_dir" -B "$generator_build" \
  -DCMAKE_BUILD_TYPE="$build_type" \
  -DETHOS_CPP_COMPILER_MODE=compiler
cmake --build "$generator_build" --target ethos --parallel

echo "[2/3] Generating $generated_source"
(
  cd "$output_dir"
  "$generator_build/bin/ethos" "$signature_path"
)

echo "[3/3] Building ethos with the executor plugin"
cmake -S "$script_dir" -B "$executor_build" \
  -DCMAKE_BUILD_TYPE="$build_type" \
  -DETHOS_CPP_COMPILER_MODE=executor \
  -DETHOS_CPP_COMPILER_GENERATED_SOURCE="$generated_source"
cmake --build "$executor_build" --target ethos --parallel

executor_binary="$executor_build/bin/ethos"
binary_name=ethos
if [[ ! -f "$executor_binary" && -f "$executor_binary.exe" ]]; then
  executor_binary="$executor_binary.exe"
  binary_name=ethos.exe
fi
final_binary="$output_dir/$binary_name"
cmake -E copy "$executor_binary" "$final_binary"

echo
echo "Built custom binary: $final_binary"
echo "Embedded signature: $signature_path"
echo "Run it with:"
echo "  $final_binary path/to/proof.eo"
echo "Inspect embedded paths with:"
echo "  $final_binary --show-config"
