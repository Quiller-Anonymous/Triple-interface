#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TARGET="Goldbach/Cert/MajorArcModules/Q0MinorZeroModeNormalizedAverage.lean"
OUT_FILE="${1:-/private/tmp/smallrest_bridge_check.out}"

cd "$ROOT_DIR"

lake env lean "$TARGET" >"$OUT_FILE" 2>&1 || true

echo "== SmallRest Bridge Check =="
echo "log: $OUT_FILE"

ERRORS="$(rg -n "error:" "$OUT_FILE" || true)"
if [[ -z "$ERRORS" ]]; then
  echo "status: clean"
  exit 0
fi

FOCUSED="$(printf '%s\n' "$ERRORS" | rg "254|258|259|260" || true)"
if [[ -n "$FOCUSED" ]]; then
  echo "status: focused-fail"
  printf '%s\n' "$FOCUSED"
else
  echo "status: fail-outside-focus"
  printf '%s\n' "$ERRORS"
fi

exit 1
