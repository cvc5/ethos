#!/usr/bin/env bash

set -euo pipefail

prog="$1"
input="$2"
pattern="$3"

set +e
output="$("$prog" "$input" 2>&1)"
status=$?
set -e

printf '%s\n' "$output"

if [ "$status" -eq 0 ]; then
  echo "Expected failure but command succeeded" >&2
  exit 1
fi

if ! printf '%s\n' "$output" | grep -Eq "$pattern"; then
  echo "Expected output to match: $pattern" >&2
  exit 1
fi
