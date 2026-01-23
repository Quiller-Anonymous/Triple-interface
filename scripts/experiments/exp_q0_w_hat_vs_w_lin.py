#!/usr/bin/env python3
"""
Experiment: compare the true hard-arc kernel W_hat(t) to the linearized kernel W_lin(t).

Definitions (fixed X,Q0, integer t>0):

  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)),

  W_lin(t) = (2/X) * Σ_{q≤Q0} c_q(t)/q
           = (2/X) * Σ_{d|t, d≤Q0} M(⌊Q0/d⌋),
    where M(u) := Σ_{m≤u} μ(m)/m.

Purpose:
  - quantify how conservative the W_lin model is for typical/structured t,
  - inform how much slack we likely have when using W_lin-based F_k experiments.

This is NOT a proof and does NOT generate a Lean certificate.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
import time
from array import array


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


def mobius_sieve(n: int) -> list[int]:
    """Return mu for 0..n via a linear sieve."""
    mu = [0] * (n + 1)
    is_comp = [False] * (n + 1)
    primes: list[int] = []
    mu[1] = 1
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            ip = i * p
            if ip > n:
                break
            is_comp[ip] = True
            if i % p == 0:
                mu[ip] = 0
                break
            mu[ip] = -mu[i]
    return mu


def mertens_weighted(mu: list[int]) -> list[float]:
    """M(u) = Σ_{m≤u} μ(m)/m as floats, for u=0..len(mu)-1."""
    m = [0.0] * len(mu)
    acc = 0.0
    for n in range(1, len(mu)):
        acc += mu[n] / n
        m[n] = acc
    return m


def compute_S_all(*, Q0: int, Tmax: int, mu: list[int]) -> array:
    """
    Compute S(t) = Σ_{q≤Q0} c_q(t)/q for all t≤Tmax via:
      Σ_{q≤Q0} c_q(t)/q = Σ_{d|t, d≤Q0} M(⌊Q0/d⌋),
      M(u) := Σ_{m≤u} μ(m)/m.
    """
    m = mertens_weighted(mu)
    s_arr = array("d", [0.0]) * (Tmax + 1)
    max_d = min(Q0, Tmax)
    for d in range(1, max_d + 1):
        coef = m[Q0 // d]
        for t in range(d, Tmax + 1, d):
            s_arr[t] += coef
    return s_arr


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
    parser = argparse.ArgumentParser(description="Experiment: compare W_hat(t) vs W_lin(t).")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--Tmax", type=int, default=None, help="Sample t in [1,Tmax]; default 2*X.")
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--parity", choices=["any", "even", "odd"], default="any")
    parser.add_argument("--include", type=str, default="", help="Comma-separated extra t values to include.")
    parser.add_argument("--top", type=int, default=10, help="Report top entries by |W_hat| and by |W_hat/W_lin|.")
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
    mu_phi, phi = mobius_phi_sieve(Q0)
    t1 = time.perf_counter()
    mu = mobius_sieve(Q0)
    t2 = time.perf_counter()
    s_arr = compute_S_all(Q0=Q0, Tmax=Tmax, mu=mu)
    t3 = time.perf_counter()
    print(f"[time] sieve(mu,phi):      {t1 - t0:.3f}s")
    print(f"[time] sieve(mu only):     {t2 - t1:.3f}s")
    print(f"[time] S(t) divisor-sieve: {t3 - t2:.3f}s")

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
    ts = list(dict.fromkeys(ts))  # preserve order, drop duplicates

    rows: list[tuple[int, float, float, float]] = []
    # each row: (t, |W_hat|, |W_lin|, ratio=|W_hat|/max(|W_lin|,tiny))
    tiny = 1e-30
    t4 = time.perf_counter()
    for t in ts:
        what = abs(w_hat(X=X, Q0=Q0, t=t, mu=mu_phi, phi=phi))
        wlin = abs((2.0 / X) * s_arr[t])
        ratio = what / max(wlin, tiny)
        rows.append((t, what, wlin, ratio))
    t5 = time.perf_counter()
    print(f"[time] computed {len(rows)} pairs (W_hat,W_lin): {t5 - t4:.3f}s")

    whats = [r[1] for r in rows]
    wlins = [r[2] for r in rows]
    ratios = [r[3] for r in rows]
    safe_ratios = [r for r in ratios if r < 1e20]  # ignore pathological wlin=0

    print("\n== Summary ==")
    print(f"max |W_hat|:            {max(whats):.6e}")
    print(f"mean |W_hat|:           {statistics.mean(whats):.6e}")
    print(f"max |W_lin|:            {max(wlins):.6e}")
    print(f"mean |W_lin|:           {statistics.mean(wlins):.6e}")
    if safe_ratios:
        print(f"mean |W_hat|/|W_lin|:   {statistics.mean(safe_ratios):.6g}")
        print(f"median |W_hat|/|W_lin|: {statistics.median(safe_ratios):.6g}")
        print(f"max |W_hat|/|W_lin|:    {max(safe_ratios):.6g}")

    top_n = min(args.top, len(rows))

    print(f"\nTop {top_n} by |W_hat|:")
    print("rank  t         |W_hat|      |W_lin|      |W_hat|/|W_lin|")
    for i, (t, what, wlin, ratio) in enumerate(sorted(rows, key=lambda r: r[1], reverse=True)[:top_n], start=1):
        print(f"{i:>4d}  {t:>8d}  {what:>12.6e}  {wlin:>12.6e}  {ratio:>12.6g}")

    print(f"\nTop {top_n} by |W_hat|/|W_lin| (excluding wlin=0):")
    print("rank  t         |W_hat|      |W_lin|      |W_hat|/|W_lin|")
    filt = [r for r in rows if r[2] > 0.0]
    for i, (t, what, wlin, ratio) in enumerate(sorted(filt, key=lambda r: r[3], reverse=True)[:top_n], start=1):
        print(f"{i:>4d}  {t:>8d}  {what:>12.6e}  {wlin:>12.6e}  {ratio:>12.6g}")


if __name__ == "__main__":
    main()

