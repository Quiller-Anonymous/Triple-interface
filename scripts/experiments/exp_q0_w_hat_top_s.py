#!/usr/bin/env python3
"""
Experiment: stress-test the true hard-arc kernel W_hat(t) at "worst" t suggested by the linearized model.

This does NOT prove anything and does NOT generate a Lean certificate.

Workflow:
  1) Compute S(t) := Σ_{q≤Q0} c_q(t)/q using the fast divisor/Mertens-weighted identity.
  2) Find the top-K t (1≤t≤Tmax) maximizing |S(t)|.
  3) For those t, compute the true hard-arc Fourier coefficient

       W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)).

This targets the question: are there “structured bad t” where |W_hat(t)| is much larger than random samples?
"""

from __future__ import annotations

import argparse
import heapq
import math
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


def mertens_weighted(mu: list[int]) -> list[float]:
    """M(u) = Σ_{m≤u} μ(m)/m as floats, for u=0..len(mu)-1."""
    m = [0.0] * len(mu)
    acc = 0.0
    for n in range(1, len(mu)):
        acc += mu[n] / n
        m[n] = acc
    return m


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


def compute_S(*, Q0: int, Tmax: int, mu: list[int]) -> array:
    """
    Compute S(t) = Σ_{q≤Q0} c_q(t)/q via:
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


def top_k_by_abs(s_arr: array, k: int) -> list[tuple[float, int]]:
    """Return [(absS, t), ...] of the top-k t by |S(t)|."""
    heap: list[tuple[float, int]] = []
    for t in range(1, len(s_arr)):
        v = abs(s_arr[t])
        if len(heap) < k:
            heapq.heappush(heap, (v, t))
        else:
            if v > heap[0][0]:
                heapq.heapreplace(heap, (v, t))
    heap.sort(reverse=True)
    return heap


def w_hat(*, X: int, Q0: int, t: int, mu: list[int], phi: list[int]) -> float:
    s = 0.0
    for q in range(1, Q0 + 1):
        cq = ramanujan_sum(q, t, mu, phi)
        if cq:
            s += cq * math.sin(2.0 * math.pi * t / (q * X))
    return s / (math.pi * t)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Experiment: compute W_hat(t) at t with largest |S(t)|.",
    )
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--Tmax", type=int, default=None, help="Max t to scan (default: 2*X).")
    parser.add_argument("--topK", type=int, default=25)
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    Tmax = 2 * X if args.Tmax is None else args.Tmax
    topK = args.topK

    if X <= 0 or Q0 <= 0 or Tmax <= 0 or topK <= 0:
        raise SystemExit("Require X,Q0,Tmax,topK positive.")
    if Tmax < 1:
        raise SystemExit("Require Tmax ≥ 1.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  Tmax={Tmax:,}  topK={topK}")

    t0 = time.perf_counter()
    mu, phi = mobius_phi_sieve(Q0)
    t1 = time.perf_counter()
    print(f"[time] sieve(mu,phi): {t1 - t0:.3f}s")

    s_arr = compute_S(Q0=Q0, Tmax=Tmax, mu=mu)
    t2 = time.perf_counter()
    print(f"[time] divisor-sieve S(t) for t≤{Tmax:,}: {t2 - t1:.3f}s")

    top = top_k_by_abs(s_arr, topK)
    t3 = time.perf_counter()
    print(f"[time] topK selection: {t3 - t2:.3f}s")

    print("\n== Top |S(t)| points and true W_hat(t) ==")
    print("rank  t        |S(t)|      S(t)        W_lin(t)        W_hat(t)        |W_hat|/|W_lin|")
    max_abs_what = 0.0
    max_t = 1
    for i, (absS, t) in enumerate(top, start=1):
        s = s_arr[t]
        wlin = (2.0 / X) * s
        what = w_hat(X=X, Q0=Q0, t=t, mu=mu, phi=phi)
        ratio = abs(what) / abs(wlin) if wlin != 0.0 else float("inf")
        print(
            f"{i:>4d}  {t:>7d}  {absS:>10.6f}  {s:>10.6f}  {wlin:>12.6e}  {what:>12.6e}  {ratio:>12.6f}"
        )
        if abs(what) > max_abs_what:
            max_abs_what = abs(what)
            max_t = t

    t4 = time.perf_counter()
    print(f"\n[time] computed W_hat for topK: {t4 - t3:.3f}s")
    print(f"max |W_hat(t)| among topK: {max_abs_what:.6g} at t={max_t}")


if __name__ == "__main__":
    main()

