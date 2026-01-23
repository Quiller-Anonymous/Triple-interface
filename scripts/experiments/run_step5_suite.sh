#!/usr/bin/env bash
set -euo pipefail

# Repro suite for Step 5 (Q0 route) Monte Carlo experiments.
#
# Purpose:
# - Quick feasibility checks for the ε₂-large TT*/Toeplitz work (not proofs).
# - Standardized, pinned command lines to keep `STEP5_SCOREBOARD.md` reproducible.
#
# Usage:
#   bash scripts/experiments/run_step5_suite.sh

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 200 --seed 1 --parity even
echo
python3 scripts/experiments/exp_q0_w_hat_moments.py --samples 200 --seed 1 --parity odd
echo

# Hybrid-W_hat TT* Monte Carlo (fast sanity).
python3 scripts/experiments/exp_q0_fk_ttstar_w_hat_mc.py \
  --k-samples 20 \
  --n-samples 100 \
  --seed 1 \
  --Qsplit 2000 \
  --estimate-f0

