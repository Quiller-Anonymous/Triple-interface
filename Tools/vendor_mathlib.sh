#!/usr/bin/env bash
set -euo pipefail
DEST=vendor/mathlib4
if [[ -d "$DEST" ]]; then
  echo "mathlib4 already present at $DEST"
  exit 0
fi
mkdir -p vendor
git clone https://github.com/leanprover-community/mathlib4.git "$DEST"
cd "$DEST"
git fetch --tags
# Prefer the tag; uncomment the SHA line if you want to pin immutably.
git checkout v4.26.0-rc2
# git checkout d5c9558e75342a10d6321e6a8c798a14f68ae23c
echo "Pinned mathlib4 to $(git rev-parse --short HEAD) (v4.26.0-rc2)"
