#!/usr/bin/env python3
"""
Experiment: gcd-structure stress test for the true hard-arc kernel W_hat(t).

We evaluate W_hat(t) on families of t designed to have lots of small prime factors:
  - multiples of selected primorials (e.g. 2·3·5·7·11, 2·…·13, 2·…·17),
  - multiples of selected lcm(1..n) values.

This is a data-gathering tool for certificate design: it probes whether |W_hat(t)| becomes
significantly worse on extreme gcd-structured t than on random/primorial-multiple scans.

W_hat(t) is computed exactly as:
  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)).
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


def w_hat(*, X: int, Q0: int, t: int, mu: list[int], phi: list[int]) -> float:
    s = 0.0
    for q in range(1, Q0 + 1):
        cq = ramanujan_sum(q, t, mu, phi)
        if cq:
            s += cq * math.sin(2.0 * math.pi * t / (q * X))
    return s / (math.pi * t)


def lcm_upto(n: int) -> int:
    acc = 1
    for k in range(2, n + 1):
        acc = acc // math.gcd(acc, k) * k
    return acc


def primorial_upto(p: int) -> int:
    # product of primes ≤ p
    sieve = [True] * (p + 1)
    sieve[:2] = [False, False]
    for x in range(2, int(math.isqrt(p)) + 1):
        if sieve[x]:
            for y in range(x * x, p + 1, x):
                sieve[y] = False
    acc = 1
    for x in range(2, p + 1):
        if sieve[x]:
            acc *= x
    return acc


@dataclass(frozen=True)
class Cand:
    t: int
    what: float
    family: str


def add_multiples(out: dict[int, str], *, base: int, Tmax: int, tag: str) -> None:
    if base <= 0 or base > Tmax:
        return
    mmax = Tmax // base
    for m in range(1, mmax + 1):
        t = m * base
        out.setdefault(t, tag)


def main() -> None:
    parser = argparse.ArgumentParser(description="Experiment: gcd-structure stress test for W_hat(t).")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--Tmax", type=int, default=None, help="Max t to test (default: 2*X).")
    parser.add_argument("--topK", type=int, default=30)
    parser.add_argument(
        "--primorials",
        type=str,
        default="11,13,17",
        help="Comma-separated primes p for primorial Π_{ℓ≤p} ℓ.",
    )
    parser.add_argument(
        "--lcms",
        type=str,
        default="10,12,14,16,18",
        help="Comma-separated n for lcm(1..n).",
    )
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    Tmax = 2 * X if args.Tmax is None else args.Tmax
    topK = args.topK
    primorial_ps = [int(x.strip()) for x in args.primorials.split(",") if x.strip()]
    lcm_ns = [int(x.strip()) for x in args.lcms.split(",") if x.strip()]

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  Tmax={Tmax:,}  topK={topK}")
    print(f"primorial p-list={primorial_ps}")
    print(f"lcm n-list={lcm_ns}")

    t0 = time.perf_counter()
    mu, phi = mobius_phi_sieve(Q0)
    t1 = time.perf_counter()
    print(f"[time] sieve(mu,phi): {t1 - t0:.3f}s")

    candidates: dict[int, str] = {}

    # Primorial multiples
    for p in primorial_ps:
        P = primorial_upto(p)
        add_multiples(candidates, base=P, Tmax=Tmax, tag=f"primorial≤{p}")

    # lcm(1..n) multiples
    for n in lcm_ns:
        L = lcm_upto(n)
        add_multiples(candidates, base=L, Tmax=Tmax, tag=f"lcm≤{n}")

    # Always include the currently known worst-case t (if in range).
    if 1 <= 1_884_960 <= Tmax:
        candidates.setdefault(1_884_960, "known-worst")

    ts = sorted(candidates.keys())
    print(f"[time] generated candidates: {time.perf_counter() - t1:.3f}s (count={len(ts):,})")

    t2 = time.perf_counter()
    vals: list[Cand] = []
    for t in ts:
        vals.append(Cand(t=t, what=w_hat(X=X, Q0=Q0, t=t, mu=mu, phi=phi), family=candidates[t]))
    t3 = time.perf_counter()
    print(f"[time] evaluated W_hat on candidates: {t3 - t2:.3f}s")

    vals.sort(key=lambda c: abs(c.what), reverse=True)
    vals = vals[:topK]

    print("\n== Top candidates by |W_hat(t)| ==")
    print("rank  t        family          |W_hat|      W_hat(t)")
    for i, c in enumerate(vals, start=1):
        fam = (c.family[:14] + "…") if len(c.family) > 15 else c.family
        print(f"{i:>4d}  {c.t:>7d}  {fam:>14s}  {abs(c.what):>10.6g}  {c.what:>12.6e}")

    if vals:
        print(f"\nmax |W_hat| among candidates: {abs(vals[0].what):.6g} at t={vals[0].t} ({vals[0].family})")


if __name__ == "__main__":
    main()

