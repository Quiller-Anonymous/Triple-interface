#!/usr/bin/env python3
"""
Experiment: structured stress-test for the true hard-arc kernel W_hat(t).

Goal: look for "bad" structured t (many small prime factors / large gcd structure) where |W_hat(t)|
is significantly larger than random sampling.

This does NOT prove anything and does NOT generate a Lean certificate.

We generate a candidate set of t values using:
  - multiples of primorials (product of primes ≤ p) up to Tmax,
  - a small family of "highly composite-ish" numbers via restricted prime-exponent recursion.

Then we compute true hard-arc
  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)),
and report the top-K by |W_hat|.

To keep runtime predictable when the candidate set is large, we optionally:
  - precompute the linearized score S(t) = Σ_{q≤Q0} c_q(t)/q for all t≤Tmax,
  - preselect only the top-E by |S(t)| among candidates,
  - evaluate true W_hat(t) only on those E values.
"""

from __future__ import annotations

import argparse
import heapq
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


def primes_up_to(n: int) -> list[int]:
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    limit = int(math.isqrt(n))
    for p in range(2, limit + 1):
        if sieve[p]:
            start = p * p
            step = p
            sieve[start : n + 1 : step] = b"\x00" * (((n - start) // step) + 1)
    return [i for i in range(2, n + 1) if sieve[i]]


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    """
    c_q(t) as an integer using:
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


def primorials(limit_prime: int) -> list[int]:
    ps = primes_up_to(limit_prime)
    out: list[int] = []
    acc = 1
    for p in ps:
        acc *= p
        out.append(acc)
    return out


def generate_primorial_multiples(*, Tmax: int, limit_prime: int) -> set[int]:
    ts: set[int] = set()
    for P in primorials(limit_prime):
        if P > Tmax:
            break
        mmax = Tmax // P
        for m in range(1, mmax + 1):
            ts.add(m * P)
    return ts


def generate_highly_compositeish(*, Tmax: int, primes: list[int], max_exps: list[int]) -> set[int]:
    """
    Generate products p1^e1 p2^e2 ... with nonincreasing exponents (classic highly composite search),
    but with explicit caps max_exps to keep the set small.
    """
    assert len(primes) == len(max_exps)
    out: set[int] = set()

    def rec(i: int, prev_e: int, acc: int) -> None:
        if acc > Tmax:
            return
        out.add(acc)
        if i == len(primes):
            return
        p = primes[i]
        emax = min(prev_e, max_exps[i])
        val = acc
        for e in range(1, emax + 1):
            if val > Tmax // p:
                break
            val *= p
            rec(i + 1, e, val)

    rec(0, 60, 1)
    out.discard(1)
    return out


@dataclass(frozen=True)
class Candidate:
    t: int
    what: float


def mertens_weighted(mu: list[int]) -> list[float]:
    """M(u) = Σ_{m≤u} μ(m)/m as floats, for u=0..len(mu)-1."""
    m = [0.0] * len(mu)
    acc = 0.0
    for n in range(1, len(mu)):
        acc += mu[n] / n
        m[n] = acc
    return m


def compute_S_all(*, Q0: int, Tmax: int, mu: list[int]) -> list[float]:
    """
    Compute S(t) = Σ_{q≤Q0} c_q(t)/q via the divisor/Mertens-weighted identity:
      Σ_{q≤Q0} c_q(t)/q = Σ_{d|t, d≤Q0} M(⌊Q0/d⌋),
      M(u) := Σ_{m≤u} μ(m)/m.
    """
    m = mertens_weighted(mu)
    s = [0.0] * (Tmax + 1)
    max_d = min(Q0, Tmax)
    for d in range(1, max_d + 1):
        coef = m[Q0 // d]
        for t in range(d, Tmax + 1, d):
            s[t] += coef
    return s


def top_e_by_absS(cand: set[int], s_all: list[float], e: int) -> list[int]:
    """Return the E candidates with largest |S(t)|."""
    if e >= len(cand):
        return sorted(cand)
    heap: list[tuple[float, int]] = []
    for t in cand:
        v = abs(s_all[t])
        if len(heap) < e:
            heapq.heappush(heap, (v, t))
        else:
            if v > heap[0][0]:
                heapq.heapreplace(heap, (v, t))
    heap.sort(reverse=True)
    return [t for _, t in heap]


def main() -> None:
    parser = argparse.ArgumentParser(description="Experiment: structured t stress-test for W_hat(t).")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--Tmax", type=int, default=None, help="Max t to test (default: 2*X).")
    parser.add_argument("--topK", type=int, default=40)
    parser.add_argument("--primorial-p", type=int, default=19, help="Generate primorials up to p.")
    parser.add_argument(
        "--primorial-min-prime",
        type=int,
        default=11,
        help="Only include multiples of primorials whose last prime ≥ this value (default: 11).",
    )
    parser.add_argument(
        "--hc-primes",
        type=str,
        default="2,3,5,7,11,13",
        help="Comma-separated primes for highly-composite-ish generation.",
    )
    parser.add_argument(
        "--hc-max-exps",
        type=str,
        default="20,12,8,6,4,4",
        help="Comma-separated max exponents aligned with --hc-primes.",
    )
    parser.add_argument(
        "--include-hc",
        action="store_true",
        help="Also include the highly-composite-ish family (can increase runtime).",
    )
    parser.add_argument(
        "--preselect-by-S",
        action="store_true",
        help="Preselect candidates by the linearized score |S(t)| before evaluating true W_hat(t).",
    )
    parser.add_argument(
        "--evalE",
        type=int,
        default=2000,
        help="If --preselect-by-S, evaluate true W_hat only on the top-E candidates by |S(t)|.",
    )
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    Tmax = 2 * X if args.Tmax is None else args.Tmax
    topK = args.topK

    hc_primes = [int(x.strip()) for x in args.hc_primes.split(",") if x.strip()]
    hc_max_exps = [int(x.strip()) for x in args.hc_max_exps.split(",") if x.strip()]
    if len(hc_primes) != len(hc_max_exps):
        raise SystemExit("hc-primes and hc-max-exps must have the same length.")
    if any(p <= 1 for p in hc_primes):
        raise SystemExit("hc-primes must be primes > 1.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  Tmax={Tmax:,}  topK={topK}")
    print(f"primorial up to p={args.primorial_p}")
    print(f"primorial min-prime={args.primorial_min_prime}")
    print(f"hc primes={hc_primes}")
    print(f"hc max exps={hc_max_exps}")
    print(f"include-hc={args.include_hc}")
    print(f"preselect-by-S={args.preselect_by_S}  evalE={args.evalE}")

    t0 = time.perf_counter()
    mu, phi = mobius_phi_sieve(Q0)
    t1 = time.perf_counter()
    print(f"[time] sieve(mu,phi): {t1 - t0:.3f}s")

    cand: set[int] = set()
    # Primorial multiples, but skip small primorials (otherwise you get millions of candidates).
    ps = primes_up_to(args.primorial_p)
    acc = 1
    for p in ps:
        acc *= p
        if p < args.primorial_min_prime:
            continue
        if acc > Tmax:
            break
        mmax = Tmax // acc
        for m in range(1, mmax + 1):
            cand.add(m * acc)

    # Optional: highly-composite-ish family (kept off by default).
    if args.include_hc:
        cand |= generate_highly_compositeish(Tmax=Tmax, primes=hc_primes, max_exps=hc_max_exps)

    cand = {t for t in cand if 1 <= t <= Tmax}

    t2 = time.perf_counter()
    print(f"[time] generated candidates: {t2 - t1:.3f}s (count={len(cand):,})")

    eval_ts = sorted(cand)
    if args.preselect_by_S:
        tS0 = time.perf_counter()
        s_all = compute_S_all(Q0=Q0, Tmax=Tmax, mu=mu)
        tS1 = time.perf_counter()
        print(f"[time] computed S(t) for all t≤{Tmax:,}: {tS1 - tS0:.3f}s")
        eval_ts = top_e_by_absS(cand, s_all, args.evalE)
        tS2 = time.perf_counter()
        print(f"[time] preselected eval set by |S(t)|: {tS2 - tS1:.3f}s (eval count={len(eval_ts):,})")

    # Evaluate W_hat(t) on the (possibly reduced) evaluation set.
    top: list[Candidate] = []
    for t in eval_ts:
        what = w_hat(X=X, Q0=Q0, t=t, mu=mu, phi=phi)
        top.append(Candidate(t=t, what=what))

    t3 = time.perf_counter()
    print(f"[time] evaluated W_hat on eval set: {t3 - t2:.3f}s")

    top.sort(key=lambda c: abs(c.what), reverse=True)
    top = top[:topK]

    print("\n== Top candidates by |W_hat(t)| ==")
    print("rank  t        |W_hat|      W_hat(t)")
    for i, c in enumerate(top, start=1):
        print(f"{i:>4d}  {c.t:>7d}  {abs(c.what):>10.6g}  {c.what:>12.6e}")

    if top:
        print(f"\nmax |W_hat| among candidates: {abs(top[0].what):.6g} at t={top[0].t}")


if __name__ == "__main__":
    main()
