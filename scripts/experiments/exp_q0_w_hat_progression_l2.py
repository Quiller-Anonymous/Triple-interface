#!/usr/bin/env python3
"""
Experiment (Step5): kernel ℓ² diagnostics along the actual TT*/Toeplitz progression.

For fixed (X,N,k), the kernel argument is:
  t = |2n + k - N|,  with n ∈ [2, N-2-k].

As n ranges uniformly, t is (essentially) uniform over the admissible parity class up to ~N-k,
so this measures the kernel moments in the *exact way they appear inside F_k* (before any
dispersion/TT* manipulation).

We estimate:
  E_n |W_hat(t)|, E_n |W_hat(t)|^2, max |W_hat(t)| over the sampled n,
and convert to the corresponding sum estimates:
  Σ_n |W_hat(t)|^2 ≈ (#n) * E_n |W_hat(t)|^2,
  Σ_n |W_hat(t)|   ≈ (#n) * E_n |W_hat(t)|.

Kernel used:
  W_hat_hybrid(t) from exp_q0_fk_ttstar_w_hat_mc.py (exact for q≤Qsplit, linearized tail).

This is NOT a proof and does NOT generate a Lean certificate.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
import time
from array import array
from pathlib import Path

from exp_q0_fk_ttstar_w_hat_mc import (
    compute_S_all,
    mobius_phi_sieve,
    mobius_sieve,
    parse_quantiles,
    quantile,
    w_hat_hybrid,
)


def parse_int_list(path: Path) -> list[int]:
    out: list[int] = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        out.append(int(line))
    return out


def sample_progression_stats(
    *,
    rng: random.Random,
    X: int,
    Q0: int,
    Qsplit: int,
    N: int,
    k: int,
    n_samples: int,
    mu: list[int],
    phi: list[int],
    s_q0: array,
    s_qs: array,
    w_cache: dict[int, float],
    include_t0: bool,
) -> dict[str, float]:
    n_hi = N - 2 - k
    if n_hi < 2:
        return {
            "count": 0.0,
            "mean_abs": 0.0,
            "mean_sq": 0.0,
            "max_abs": 0.0,
            "sum_abs_est": 0.0,
            "sum_sq_est": 0.0,
        }
    n_lo = 2
    count = n_hi - n_lo + 1

    acc_abs = 0.0
    acc_sq = 0.0
    max_abs = 0.0

    for _ in range(n_samples):
        n = rng.randrange(n_lo, n_hi + 1)
        t = (2 * n + k) - N
        if t < 0:
            t = -t
        if t == 0 and not include_t0:
            w = 0.0
        else:
            w = w_cache.get(t)
            if w is None:
                w = w_hat_hybrid(X=X, Q0=Q0, Qsplit=Qsplit, t=t, mu=mu, phi=phi, s_q0=s_q0, s_qs=s_qs)
                w_cache[t] = w
        aw = abs(w)
        acc_abs += aw
        acc_sq += w * w
        if aw > max_abs:
            max_abs = aw

    mean_abs = acc_abs / n_samples
    mean_sq = acc_sq / n_samples
    return {
        "count": float(count),
        "mean_abs": mean_abs,
        "mean_sq": mean_sq,
        "max_abs": max_abs,
        "sum_abs_est": float(count) * mean_abs,
        "sum_sq_est": float(count) * mean_sq,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description="Experiment: W_hat moments along t=|2n+k-N| progression.")
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--Q0", type=int, default=30_000)
    ap.add_argument("--Qsplit", type=int, default=500)
    ap.add_argument("--H", type=int, default=10_000, help="Default N=X+H unless overridden.")
    ap.add_argument("--N", type=int, default=None)
    ap.add_argument("--Tmax", type=int, default=2_000_000, help="S_Q precompute limit (default 2*X).")
    ap.add_argument("--seed", type=int, default=60)
    ap.add_argument("--n-samples", type=int, default=10_000, help="n samples per k.")
    ap.add_argument("--k-samples", type=int, default=200, help="Random k values to sample (k>0).")
    ap.add_argument("--k-file", type=str, default=None, help="Optional file with explicit k values.")
    ap.add_argument("--include-structured", action="store_true", help="Add k near 30k*m clusters.")
    ap.add_argument("--quantiles", type=str, default="0.5,0.9,0.99,0.999", help="Quantiles for per-k sum_sq_est.")
    ap.add_argument("--include-t0", action="store_true", help="Include t=0 values (unbalanced constant mode).")
    args = ap.parse_args()

    X = args.X
    Q0 = args.Q0
    Qsplit = args.Qsplit
    H = args.H
    N = args.N if args.N is not None else X + H
    Tmax = args.Tmax if args.Tmax is not None else 2 * X

    rng = random.Random(args.seed)
    qs = parse_quantiles(args.quantiles)

    print("== Parameters ==")
    print(
        f"X={X:,}  Q0={Q0:,}  Qsplit={Qsplit:,}  N={N:,}  Tmax={Tmax:,}  "
        f"k_samples={args.k_samples:,}  n_samples={args.n_samples:,}  seed={args.seed}"
    )
    print(f"include_structured={args.include_structured}  include_t0={args.include_t0}")

    t0 = time.time()
    mu, phi = mobius_phi_sieve(Qsplit)
    print(f"[time] sieve(mu,phi) to Qsplit: {time.time()-t0:.3f}s")

    t1 = time.time()
    mu_q0 = mobius_sieve(Q0)
    print(f"[time] sieve(mu) to Q0:        {time.time()-t1:.3f}s")

    t2 = time.time()
    s_q0 = compute_S_all(Q=Q0, Tmax=Tmax, mu=mu_q0)
    print(f"[time] S_Q0(t) to Tmax:         {time.time()-t2:.3f}s")

    t3 = time.time()
    s_qs = compute_S_all(Q=Qsplit, Tmax=Tmax, mu=mu_q0)
    print(f"[time] S_Qsplit(t) to Tmax:     {time.time()-t3:.3f}s")

    # Build k set
    k_set: set[int] = set()
    if args.k_file:
        k_set.update(parse_int_list(Path(args.k_file)))
    for _ in range(args.k_samples):
        k_set.add(rng.randrange(1, max(2, N - 3)))
    if args.include_structured:
        for m in range(1, 34):
            base = 30_000 * m
            for off in range(-1000, 1001, 200):
                k_set.add(base + off)

    k_list = sorted(k for k in k_set if 1 <= k <= (N - 4))
    if not k_list:
        raise ValueError("no admissible k values")
    print(f"k count: {len(k_list)}  (min={k_list[0]}, max={k_list[-1]})")

    w_cache: dict[int, float] = {}

    # Per-k estimates
    sum_sq_est_list: list[float] = []
    sum_abs_est_list: list[float] = []
    mean_sq_list: list[float] = []
    mean_abs_list: list[float] = []
    max_abs_list: list[float] = []

    t4 = time.time()
    for k in k_list:
        stats = sample_progression_stats(
            rng=rng,
            X=X,
            Q0=Q0,
            Qsplit=Qsplit,
            N=N,
            k=k,
            n_samples=args.n_samples,
            mu=mu,
            phi=phi,
            s_q0=s_q0,
            s_qs=s_qs,
            w_cache=w_cache,
            include_t0=args.include_t0,
        )
        if stats["count"] <= 0:
            continue
        sum_sq_est_list.append(stats["sum_sq_est"])
        sum_abs_est_list.append(stats["sum_abs_est"])
        mean_sq_list.append(stats["mean_sq"])
        mean_abs_list.append(stats["mean_abs"])
        max_abs_list.append(stats["max_abs"])
    print(f"[time] sampled progression moments: {time.time()-t4:.3f}s")
    print(f"kernel cache size: {len(w_cache):,} distinct t values")

    def summarize(name: str, xs: list[float]) -> None:
        xs_sorted = sorted(xs)
        print(f"{name}: mean={statistics.mean(xs):.6e}  median={statistics.median(xs):.6e}  max={xs_sorted[-1]:.6e}")
        if qs:
            print(f"{name} quantiles:")
            for q in qs:
                print(f"  q={q:>7}: {quantile(xs_sorted, q):.6e}")

    print("\n== Per-k estimated sums along t=|2n+k-N| progression ==")
    summarize("sum_sq_est = Σ_n |W(t)|^2", sum_sq_est_list)
    summarize("sum_abs_est = Σ_n |W(t)|", sum_abs_est_list)
    print("\n== Per-k mean moments along progression ==")
    summarize("mean_sq = E_n |W(t)|^2", mean_sq_list)
    summarize("mean_abs = E_n |W(t)|", mean_abs_list)
    summarize("max_abs_sample = max_sampled_n |W(t)|", max_abs_list)


if __name__ == "__main__":
    main()

