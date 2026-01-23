#!/usr/bin/env python3
"""
Experiment: decompose the true hard-arc kernel W_hat(t) into q-block contributions.

We study (for fixed X,Q0, integer t>0):

  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)).

This script computes:
  - the total W_hat(t),
  - cumulative partial sums in q,
  - dyadic block sums (q in (2^j, 2^{j+1}]),
  - cancellation metrics: |Σ block| / Σ |block|, and Σ |term_q| vs |Σ term_q|.

Purpose: identify where the size comes from (small q vs large q), and how much cancellation
occurs across q. This guides certificate inequality design (e.g. block splitting).
"""

from __future__ import annotations

import argparse
import math
import time
from dataclasses import dataclass


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


@dataclass(frozen=True)
class Block:
    q_lo_excl: int
    q_hi_incl: int
    sum_terms: float
    sum_abs_terms: float
    nonzero_terms: int


def compute_blocks(*, X: int, Q0: int, t: int, mu: list[int], phi: list[int]) -> tuple[list[Block], float, float]:
    """
    Return (blocks, sum_terms_raw, sum_abs_terms_raw) where:
      sum_terms_raw = Σ_{q≤Q0} c_q(t) sin(2π t/(qX))
      W_hat(t) = sum_terms_raw / (π t)
    and blocks are dyadic in q.
    """
    # dyadic partition for q up to Q0, using disjoint blocks:
    #   (0,1], (1,2], (2,4], ..., (2^j, 2^{j+1}], ... and the last block truncated to Q0.
    blocks: list[Block] = []
    sum_terms_raw = 0.0
    sum_abs_raw = 0.0
    q_lo = 0
    q_hi = 1
    while q_lo < Q0:
        q_hi = min(q_hi, Q0)
        s = 0.0
        sa = 0.0
        nz = 0
        for qq in range(q_lo + 1, q_hi + 1):
            cq = ramanujan_sum(qq, t, mu, phi)
            if cq == 0:
                continue
            term = cq * math.sin(2.0 * math.pi * t / (qq * X))
            s += term
            sa += abs(term)
            nz += 1
        blocks.append(Block(q_lo_excl=q_lo, q_hi_incl=q_hi, sum_terms=s, sum_abs_terms=sa, nonzero_terms=nz))
        sum_terms_raw += s
        sum_abs_raw += sa
        q_lo = q_hi
        q_hi = 2 * q_hi
    return blocks, sum_terms_raw, sum_abs_raw


def main() -> None:
    parser = argparse.ArgumentParser(description="Experiment: q-decomposition of true hard-arc W_hat(t).")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--t", type=int, action="append", required=True, help="t value (repeatable).")
    parser.add_argument("--show-top-blocks", type=int, default=12, help="Show top blocks by |sum|.")
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    ts = args.t

    if X <= 0 or Q0 <= 0:
        raise SystemExit("Require X,Q0 positive.")
    if any(t <= 0 for t in ts):
        raise SystemExit("Require all t positive.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  count(t)={len(ts)}")
    print(f"t list: {ts}")

    t0 = time.perf_counter()
    mu, phi = mobius_phi_sieve(Q0)
    t1 = time.perf_counter()
    print(f"[time] sieve(mu,phi): {t1 - t0:.3f}s")

    for t in ts:
        tb0 = time.perf_counter()
        blocks, sum_terms_raw, sum_abs_raw = compute_blocks(X=X, Q0=Q0, t=t, mu=mu, phi=phi)
        tb1 = time.perf_counter()

        what = sum_terms_raw / (math.pi * t)
        what_abs_upper = sum_abs_raw / (math.pi * t)
        cancel_ratio = abs(sum_terms_raw) / sum_abs_raw if sum_abs_raw != 0.0 else float("nan")

        print("\n== t =", t, "==")
        print(f"[time] blocks: {tb1 - tb0:.3f}s  (#blocks={len(blocks)})")
        print(f"W_hat(t):                 {what:.6e}")
        print(f"|W_hat(t)|:               {abs(what):.6e}")
        print(f"(Σ|term_q|)/(π t):        {what_abs_upper:.6e}   (trivial abs upper bound)")
        print(f"cancellation ratio:       {cancel_ratio:.6g}     (=|Σ term| / Σ|term|)")

        # sort blocks by |sum_terms|
        blocks_by_mag = sorted(blocks, key=lambda b: abs(b.sum_terms), reverse=True)
        print(f"\nTop {args.show_top_blocks} dyadic q-blocks by |block sum| (raw, before / (π t)):")
        print("rank  q-range        block-sum       |block| sumabs(block)  nz")
        for i, b in enumerate(blocks_by_mag[: args.show_top_blocks], start=1):
            q_rng = f"({b.q_lo_excl},{b.q_hi_incl}]"
            print(
                f"{i:>4d}  {q_rng:>12s}  {b.sum_terms:>12.6e}  {abs(b.sum_terms):>12.6e}  {b.sum_abs_terms:>12.6e}  {b.nonzero_terms:>5d}"
            )

        # cumulative in q by blocks
        print("\nCumulative by increasing dyadic q-blocks:")
        cum = 0.0
        cum_abs = 0.0
        for b in blocks:
            cum += b.sum_terms
            cum_abs += b.sum_abs_terms
            q_rng = f"({b.q_lo_excl},{b.q_hi_incl}]"
            ratio = abs(cum) / cum_abs if cum_abs != 0.0 else float("nan")
            print(f"{q_rng:>12s}  cum={cum:>12.6e}  cum_abs={cum_abs:>12.6e}  |cum|/cum_abs={ratio:>9.6f}")


if __name__ == "__main__":
    main()
