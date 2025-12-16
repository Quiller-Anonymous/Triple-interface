#!/usr/bin/env bash
set -euo pipefail

echo "== Doctor: toolchain =="
if [[ -f lean-toolchain ]]; then cat lean-toolchain; else echo "missing lean-toolchain"; exit 1; fi

echo "== Doctor: lakefile =="
test -f lakefile.lean && echo "lakefile.lean present" || { echo "missing lakefile.lean"; exit 1; }

echo "== Doctor: mathlib vendor =="
if [[ -d vendor/mathlib4 ]]; then
  (cd vendor/mathlib4 && git describe --tags --always --dirty || git rev-parse --short HEAD || true)
else
  echo "vendor/mathlib4 missing"; exit 1
fi

echo "== Versions (pinned env) =="
# Make sure we're invoking Lean/Lake under the pinned toolchain
lake env lean --version || { echo "Lean not available"; exit 1; }
lake --version || true

# Optional: fetch precompiled oleans if the cache tool is present
if lake env bash -lc 'lake exe cache --help' >/dev/null 2>&1; then
  echo "== (Optional) Fetch mathlib cache =="
  lake env lake exe cache get || true
fi

echo "== Import smoke test =="
TMP="$(mktemp _check.XXXXXX.lean)"
trap 'rm -f "$TMP"' EXIT
cat > "$TMP" <<'LEAN'
import Mathlib.Algebra.BigOperators
open scoped BigOperators
-- touch Finset/∑ so we know the namespace is live
def _t (n : ℕ) : ℝ := ∑ k in Finset.range (n+1), (k : ℝ)
#eval IO.println "OK: imported BigOperators and used ∑"
LEAN
lake env lean "$TMP"

echo "== Doctor: lake build dry-run =="
lake --version || true
