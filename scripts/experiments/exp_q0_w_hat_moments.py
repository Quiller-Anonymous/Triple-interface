#!/usr/bin/env python3
"""
Experiment: estimate ℓ² / weighted-ℓ² moments of the true hard-arc kernel W_hat(t).

We sample integer t uniformly from a range [1,Tmax] (optionally restricting parity) and compute:

  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)).

Then we estimate (by Monte Carlo) quantities relevant to Toeplitz/TT* bounds, e.g.:
  - mean |W_hat(t)|^2 over t,
  - approximate Σ_{1≤t≤Tmax} |W_hat(t)|^2 ≈ Tmax * mean,
  - weighted moments mean (t^p * |W_hat(t)|^2), for p=1,2 (optional),
which correspond to norms that often arise after summation by parts / discrete Plancherel.

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


def w_hat(*, X: int, Q0: int, t: int, mu: list[int], phi: list[int]) -> float:
    s = 0.0
    for q in range(1, Q0 + 1):
        cq = ramanujan_sum(q, t, mu, phi)
        if cq:
            s += cq * math.sin(2.0 * math.pi * t / (q * X))
    return s / (math.pi * t)


def main() -> None:
    parser = argparse.ArgumentParser(description="Experiment: Monte Carlo moments of W_hat(t).")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--Tmax", type=int, default=None, help="Sample t in [1,Tmax]; default 2*X.")
    parser.add_argument("--samples", type=int, default=500)
    parser.add_argument("--seed", type=int, default=6)
    parser.add_argument("--parity", choices=["any", "even", "odd"], default="even")
    parser.add_argument("--include", type=str, default="", help="Comma-separated extra t values to include.")
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

    abs_sq: list[float] = []
    t_abs_sq: list[float] = []
    t2_abs_sq: list[float] = []
    max_abs = 0.0
    max_t = 1

    t2 = time.perf_counter()
    for t in ts:
        w = w_hat(X=X, Q0=Q0, t=t, mu=mu, phi=phi)
        aw = abs(w)
        if aw > max_abs:
            max_abs = aw
            max_t = t
        w2 = aw * aw
        abs_sq.append(w2)
        t_abs_sq.append(t * w2)
        t2_abs_sq.append((t * t) * w2)
    t3 = time.perf_counter()
    print(f"[time] computed {len(ts)} W_hat values: {t3 - t2:.3f}s")

    mean_w2 = statistics.mean(abs_sq)
    med_w2 = statistics.median(abs_sq)
    mean_t_w2 = statistics.mean(t_abs_sq)
    mean_t2_w2 = statistics.mean(t2_abs_sq)

    print("\n== Estimated moments ==")
    print(f"max |W_hat|:        {max_abs:.6e} at t={max_t}")
    print(f"mean |W_hat|^2:     {mean_w2:.6e}")
    print(f"median |W_hat|^2:   {med_w2:.6e}")
    print(f"mean (t*|W_hat|^2): {mean_t_w2:.6e}")
    print(f"mean (t^2*|W_hat|^2): {mean_t2_w2:.6e}")

    # Monte Carlo estimate for full sums over 1..Tmax (unweighted and weighted):
    print("\n== Extrapolated full-range sums (heuristic) ==")
    print(f"Sum_{{t<=Tmax}} |W_hat(t)|^2 ≈ {Tmax * mean_w2:.6e}")
    print(f"Sum_{{t<=Tmax}} t*|W_hat(t)|^2 ≈ {Tmax * mean_t_w2:.6e}")
    print(f"Sum_{{t<=Tmax}} t^2*|W_hat(t)|^2 ≈ {Tmax * mean_t2_w2:.6e}")


if __name__ == "__main__":
    main()
