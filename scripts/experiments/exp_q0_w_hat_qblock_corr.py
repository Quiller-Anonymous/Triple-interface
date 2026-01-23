#!/usr/bin/env python3
"""
Experiment: q-block (dyadic) correlation structure for the true hard-arc kernel W_hat(t).

We write the raw (un-normalized) kernel sum as:

  raw(t) := Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)),
  W_hat(t) = raw(t) / (π t).

Define dyadic q-blocks (2^{j-1} < q ≤ 2^j) (with j starting at 0 for q=1),
and let

  raw_j(t) := Σ_{q in block j} c_q(t) * sin(2π t/(q X)).

Then raw(t) = Σ_j raw_j(t).

This script samples many t values and computes:
  - per-block empirical second moments E[raw_j(t)^2],
  - empirical cross moments E[raw_j(t) raw_{j'}(t)] (j≠j'),
  - a summary of how large off-diagonal correlations are relative to diagonals.

Optionally, it can compute the same statistics for the *weighted* block contributions to W_hat:

  w_j(t) := raw_j(t) / (π t),
  W_hat(t) = Σ_j w_j(t).

This is closer to the Toeplitz/TT* kernel that appears after the β-expansion.

Purpose:
  - provide feasibility evidence for a “dispersion after squaring” step,
  - locate which q-scales dominate cancellation for the worst observed t values.

This is NOT a proof and does NOT generate a Lean certificate.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
import time


def mobius_phi_sieve(n: int) -> tuple[list[int], list[int]]:
    """Return (mu, phi) for 0..n via a linear sieve."""
    mu = [0] * (n + 1)
    phi = [0] * (n + 1)
    is_comp = [False] * (n + 1)
    primes: list[int] = []
    mu[1] = 1
    phi[1] = 1
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
            phi[i] = i - 1
        for p in primes:
            ip = i * p
            if ip > n:
                break
            is_comp[ip] = True
            if i % p == 0:
                mu[ip] = 0
                phi[ip] = phi[i] * p
                break
            mu[ip] = -mu[i]
            phi[ip] = phi[i] * (p - 1)
    return mu, phi


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    """
    c_q(t) using:
      let g = gcd(q,t), h = q/g; then c_q(t) = μ(h) * φ(q)/φ(h).
    """
    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def dyadic_blocks(Q0: int) -> list[tuple[int, int]]:
    """
    Return blocks as (lo, hi] with integer endpoints, covering q=1..Q0.
    Block 0 is (0,1], block 1 is (1,2], block 2 is (2,4], etc.
    """
    blocks: list[tuple[int, int]] = []
    hi = 1
    lo = 0
    while hi < Q0:
        blocks.append((lo, hi))
        lo = hi
        hi = min(Q0, 2 * hi)
    blocks.append((lo, Q0))
    return blocks


def compute_raw_blocks(*, X: int, Q0: int, t: int, mu: list[int], phi: list[int], blocks: list[tuple[int, int]]) -> list[float]:
    two_pi_t_over_X = 2.0 * math.pi * t / X
    out = [0.0] * len(blocks)
    for bi, (lo, hi) in enumerate(blocks):
        s = 0.0
        for q in range(lo + 1, hi + 1):
            cq = ramanujan_sum(q, t, mu, phi)
            if cq:
                s += cq * math.sin(two_pi_t_over_X / q)
        out[bi] = s
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Experiment: q-block correlation for W_hat(t).")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--Tmax", type=int, default=None, help="Sample t in [1,Tmax]; default 2*X.")
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--seed", type=int, default=5)
    parser.add_argument("--parity", choices=["any", "even", "odd"], default="even")
    parser.add_argument("--include", type=str, default="", help="Comma-separated extra t values to include.")
    parser.add_argument("--report-top", type=int, default=5, help="How many largest off-diagonal entries to show.")
    parser.add_argument(
        "--weighted",
        action="store_true",
        help="Use weighted blocks w_j(t)=raw_j(t)/(π t) (i.e. W_hat-units) instead of raw_j(t).",
    )
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    Tmax = (2 * X) if args.Tmax is None else args.Tmax
    if X <= 0 or Q0 <= 0 or Tmax <= 0:
        raise SystemExit("Require X,Q0,Tmax positive.")

    blocks = dyadic_blocks(Q0)
    B = len(blocks)
    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  Tmax={Tmax:,}  samples={args.samples}  parity={args.parity}  seed={args.seed}")
    print(f"blocks={B}  (dyadic, last block ends at Q0)")
    print(f"weighted={args.weighted}")

    t0 = time.perf_counter()
    mu, phi = mobius_phi_sieve(Q0)
    t1 = time.perf_counter()
    print(f"[time] sieve(mu,phi): {t1 - t0:.3f}s")

    rng = random.Random(args.seed)

    extra_ts: list[int] = []
    if args.include.strip():
        for part in args.include.split(","):
            part = part.strip()
            if not part:
                continue
            t = int(part)
            if t <= 0 or t > Tmax:
                raise SystemExit(f"--include t must be in [1,Tmax], got {t}")
            extra_ts.append(t)

    def sample_t() -> int:
        while True:
            t = rng.randrange(1, Tmax + 1)
            if args.parity == "even" and (t % 2 == 1):
                continue
            if args.parity == "odd" and (t % 2 == 0):
                continue
            return t

    ts = [sample_t() for _ in range(args.samples)] + extra_ts
    ts = list(dict.fromkeys(ts))
    print(f"t count: {len(ts)} (after de-dup and include)")

    # accumulate moments
    # M[j][j'] = mean(v_j * v_j') where v_j is raw_j or weighted w_j
    M = [[0.0 for _ in range(B)] for _ in range(B)]
    # also track per-block mean absolute contribution
    mean_abs = [0.0 for _ in range(B)]
    t2 = time.perf_counter()
    for t in ts:
        v = compute_raw_blocks(X=X, Q0=Q0, t=t, mu=mu, phi=phi, blocks=blocks)
        if args.weighted:
            scale = 1.0 / (math.pi * t)
            v = [x * scale for x in v]
        for j in range(B):
            mean_abs[j] += abs(v[j])
        for j in range(B):
            vj = v[j]
            for j2 in range(B):
                M[j][j2] += vj * v[j2]
    t3 = time.perf_counter()
    print(f"[time] processed {len(ts)} t values: {t3 - t2:.3f}s")

    inv = 1.0 / len(ts)
    for j in range(B):
        mean_abs[j] *= inv
        for j2 in range(B):
            M[j][j2] *= inv

    diag = [M[j][j] for j in range(B)]
    diag_sum = sum(diag)
    off_abs_sum = 0.0
    off_max = 0.0
    off_max_pair = (0, 0)
    off_entries: list[tuple[float, int, int]] = []
    for j in range(B):
        for j2 in range(B):
            if j == j2:
                continue
            a = abs(M[j][j2])
            off_abs_sum += a
            if a > off_max:
                off_max = a
                off_max_pair = (j, j2)
            off_entries.append((a, j, j2))
    off_entries.sort(reverse=True)

    if args.weighted:
        print("\n== Summary (weighted block moments, W_hat-units) ==")
    else:
        print("\n== Summary (raw-block moments) ==")
    print(f"sum diag E[raw_j^2]:      {diag_sum:.6e}")
    print(f"sum off abs |E[raw_j raw_j']|: {off_abs_sum:.6e}")
    if diag_sum != 0.0:
        print(f"(sum off abs)/(sum diag): {off_abs_sum/diag_sum:.6g}")
        print(f"max off abs / (sum diag): {off_max/diag_sum:.6g}")
    print(f"max off abs entry:        {off_max:.6e} at (j,j')={off_max_pair}")

    top = min(args.report_top, len(off_entries))
    print(f"\nTop {top} off-diagonal entries by |E[raw_j raw_j']|:")
    print("rank  (j,j')   |E|          E           sqrt(Ejj*Ejj')   corr≈E/sqrt(EjjEjj')")
    for i, (a, j, j2) in enumerate(off_entries[:top], start=1):
        denom = math.sqrt(max(0.0, diag[j] * diag[j2]))
        corr = (M[j][j2] / denom) if denom != 0.0 else float("nan")
        print(f"{i:>4d}  ({j:>2d},{j2:>2d})  {a:>11.4e}  {M[j][j2]:>11.4e}  {denom:>11.4e}  {corr:>11.4e}")

    # Also show which blocks dominate mean |raw_j|
    idx = list(range(B))
    idx.sort(key=lambda j: mean_abs[j], reverse=True)
    print("\nTop blocks by mean |raw_j|:")
    print("rank  j   (lo,hi]        mean|raw_j|")
    for rnk, j in enumerate(idx[: min(10, B)], start=1):
        lo, hi = blocks[j]
        print(f"{rnk:>4d}  {j:>2d}  ({lo:>5d},{hi:>5d}]  {mean_abs[j]:>12.6e}")


if __name__ == "__main__":
    main()
