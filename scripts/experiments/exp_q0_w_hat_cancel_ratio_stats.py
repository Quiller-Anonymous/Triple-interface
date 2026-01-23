#!/usr/bin/env python3
"""
Experiment: cancellation statistics for the true hard-arc kernel W_hat(t).

We study (for fixed X,Q0, integer t>0):

  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)),

and report, over random samples of t:
  - max |W_hat(t)| observed,
  - typical size of |W_hat(t)|,
  - cancellation ratio: |Σ term_q| / Σ |term_q|,
  - the trivial abs upper bound Σ|term_q|/(π t) vs |W_hat(t)|.

Purpose:
  - quantify how much q-sum cancellation is typical and how bad it can get,
  - inform which “Knob A/B/C” tightening steps are worth pursuing for ε₂-large.

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


def w_hat_stats_for_t(*, X: int, Q0: int, t: int, mu: list[int], phi: list[int]) -> tuple[float, float, float]:
    """
    Return (w_hat, w_abs_upper, cancel_ratio) where:
      w_hat = Σ term_q / (π t)
      w_abs_upper = Σ |term_q| / (π t)
      cancel_ratio = |Σ term_q| / Σ |term_q| (NaN if Σ|term_q|=0).
    """
    sum_terms_raw = 0.0
    sum_abs_raw = 0.0
    for q in range(1, Q0 + 1):
        cq = ramanujan_sum(q, t, mu, phi)
        if cq == 0:
            continue
        term = cq * math.sin(2.0 * math.pi * t / (q * X))
        sum_terms_raw += term
        sum_abs_raw += abs(term)
    w_hat = sum_terms_raw / (math.pi * t)
    w_abs_upper = sum_abs_raw / (math.pi * t)
    cancel_ratio = abs(sum_terms_raw) / sum_abs_raw if sum_abs_raw != 0.0 else float("nan")
    return w_hat, w_abs_upper, cancel_ratio


def main() -> None:
    parser = argparse.ArgumentParser(description="Experiment: random-sample cancellation stats for W_hat(t).")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--Tmax", type=int, default=None, help="Sample t in [1,Tmax]; default 2*X.")
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--seed", type=int, default=123)
    parser.add_argument("--parity", choices=["any", "even", "odd"], default="any")
    parser.add_argument("--top", type=int, default=8, help="Report top-|W_hat| samples.")
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    Tmax = (2 * X) if args.Tmax is None else args.Tmax
    if X <= 0 or Q0 <= 0 or Tmax <= 0:
        raise SystemExit("Require X,Q0,Tmax positive.")
    if args.samples <= 0:
        raise SystemExit("Require --samples > 0.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  Tmax={Tmax:,}  samples={args.samples}  parity={args.parity}  seed={args.seed}")

    t0 = time.perf_counter()
    mu, phi = mobius_phi_sieve(Q0)
    t1 = time.perf_counter()
    print(f"[time] sieve(mu,phi): {t1 - t0:.3f}s")

    rng = random.Random(args.seed)

    def sample_t() -> int:
        while True:
            t = rng.randrange(1, Tmax + 1)
            if args.parity == "even" and (t % 2 == 1):
                continue
            if args.parity == "odd" and (t % 2 == 0):
                continue
            return t

    samples: list[tuple[int, float, float, float]] = []
    # each entry: (t, |W_hat|, abs_upper, cancel_ratio)
    t2 = time.perf_counter()
    for _ in range(args.samples):
        t = sample_t()
        w_hat, w_abs_upper, cancel_ratio = w_hat_stats_for_t(X=X, Q0=Q0, t=t, mu=mu, phi=phi)
        samples.append((t, abs(w_hat), w_abs_upper, cancel_ratio))
    t3 = time.perf_counter()
    print(f"[time] computed {args.samples} W_hat(t): {t3 - t2:.3f}s")

    abs_vals = [x[1] for x in samples]
    upper_vals = [x[2] for x in samples]
    ratios = [x[3] for x in samples if not math.isnan(x[3])]

    print("\n== Summary over sampled t ==")
    print(f"max |W_hat|:               {max(abs_vals):.6e}")
    print(f"mean |W_hat|:              {statistics.mean(abs_vals):.6e}")
    print(f"median |W_hat|:            {statistics.median(abs_vals):.6e}")
    print(f"mean abs-upper:            {statistics.mean(upper_vals):.6e}   (Σ|term_q|/(π t))")
    print(f"mean cancellation ratio:   {statistics.mean(ratios):.6g}     (=|Σ term|/Σ|term|)")
    print(f"min cancellation ratio:    {min(ratios):.6g}")
    print(f"median cancellation ratio: {statistics.median(ratios):.6g}")

    top_n = min(args.top, len(samples))
    top_by_abs = sorted(samples, key=lambda x: x[1], reverse=True)[:top_n]
    print(f"\nTop {top_n} samples by |W_hat|:")
    print("rank  t         |W_hat|      abs-upper    ratio(|sum|/sumabs)")
    for i, (t, abs_w, abs_upper, ratio) in enumerate(top_by_abs, start=1):
        print(f"{i:>4d}  {t:>8d}  {abs_w:>12.6e}  {abs_upper:>12.6e}  {ratio:>12.6g}")


if __name__ == "__main__":
    main()

