#!/usr/bin/env bash
set -euo pipefail

# Batch-build all chunk files with Lean, in parallel, to avoid long single runs.
# Usage: ./build_chunks.sh [BATCH_SIZE] [PARALLELISM]
#
# Defaults: 50 files per batch, 3 batches in parallel.

batch_size="${1:-50}"
parallelism="${2:-3}"

# Find the chunk files (prefer fd, fall back to find), sorted for determinism.
if command -v fd >/dev/null 2>&1; then
  file_list="$(fd 'Chunk.*_verified\.lean' Goldbach/FiniteBase/Chunks | sort)"
else
  file_list="$(find Goldbach/FiniteBase/Chunks -name 'Chunk*_verified.lean' | sort)"
fi

if [[ -z "${file_list}" ]]; then
  echo "No chunk files found under Goldbach/FiniteBase/Chunks" >&2
  exit 1
fi

echo "$file_list" | xargs -n"${batch_size}" -P"${parallelism}" -I{} sh -c 'echo "Building {}" && lake env lean "{}"'
