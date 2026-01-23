#!/usr/bin/env python3
"""
Experiment: compute the exact (floating) band sums for the hybrid kernel

  W_mix(t) = W_small(t) + W_large_lin(t)

on the TT*/Toeplitz bandwidth t ∈ [1, N0] (default N0=X0+H), split by parity.

This is the deterministic "passes-budget" scaffold used in Step5:
  - W_small: exact q≤q_small hard-arc term with sin(2π t/(qX)),
  - W_large_lin: linearized q>q_small term (2/X)*Σ_{q>q_small} c_q(t)/q via divisor-add.

Outputs:
  - Σ_{t even≤N0} |W_mix(t)|^2,
  - BW_mix := 2 * Σ_{t even≤N0} |W_mix(t)|^2 (the k=0 progression sum),
  - max |W_mix(t)| and its argmax on 1..N0.

This is NOT a proof and does NOT generate a Lean certificate.
"""

from __future__ import annotations

import argparse
import math
import time
from array import array


def mobius_sieve(n: int) -> list[int]:
    mu = [1] * (n + 1)
    is_prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if is_prime[p]:
            for k in range(p, n + 1, p):
                is_prime[k] = False
                mu[k] *= -1
            p2 = p * p
            if p2 <= n:
                for k in range(p2, n + 1, p2):
                    mu[k] = 0
    mu[0] = 0
    return mu


def totients_up_to(n: int) -> list[int]:
    phi = list(range(n + 1))
    for p in range(2, n + 1):
        if phi[p] == p:
            for k in range(p, n + 1, p):
                phi[k] -= phi[k] // p
    return phi


def prefix_mertens_over_m(mu: list[int]) -> array:
    n = len(mu) - 1
    M = array("d", [0.0]) * (n + 1)
    acc = 0.0
    for m in range(1, n + 1):
        acc += float(mu[m]) / float(m)
        M[m] = acc
    return M


def build_S_all(*, Q0: int, Tmax: int, mu: list[int]) -> array:
    """S_all[t] := Σ_{q≤Q0} c_q(t)/q via divisor-add identity."""
    M = prefix_mertens_over_m(mu)
    A = array("d", [0.0]) * (Q0 + 1)
    for d in range(1, Q0 + 1):
        A[d] = M[Q0 // d]
    S = array("d", [0.0]) * (Tmax + 1)
    for d in range(1, Q0 + 1):
        ad = A[d]
        for t in range(d, Tmax + 1, d):
            S[t] += ad
    return S


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def main() -> None:
    ap = argparse.ArgumentParser(description="Compute band sums for W_mix(t) on t≤N0.")
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--Q0", type=int, default=30_000)
    ap.add_argument("--H", type=int, default=10_000)
    ap.add_argument("--N0", type=int, default=None)
    ap.add_argument("--q-small", type=int, default=12)
    args = ap.parse_args()

    X = args.X
    Q0 = args.Q0
    q_small = args.q_small
    N0 = args.N0 if args.N0 is not None else (X + args.H)
    if not (1 <= q_small < Q0):
        raise SystemExit("--q-small must satisfy 1 ≤ q_small < Q0")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  N0={N0:,}  q_small={q_small}")

    t0 = time.perf_counter()
    mu = mobius_sieve(Q0)
    phi = totients_up_to(Q0)
    t1 = time.perf_counter()
    print(f"[time] sieve(mu,phi): {t1 - t0:.3f}s")

    t2 = time.perf_counter()
    S_all = build_S_all(Q0=Q0, Tmax=N0, mu=mu)
    t3 = time.perf_counter()
    print(f"[time] build S_all(t)=Σ c_q(t)/q: {t3 - t2:.3f}s")

    inv_pi = 1.0 / math.pi
    scale_lin = 2.0 / float(X)

    sum_sq_even = 0.0
    sum_sq_odd = 0.0
    max_abs = 0.0
    max_t = 1

    t4 = time.perf_counter()
    for t in range(1, N0 + 1):
        # small-q exact
        w_small = 0.0
        s_small_over_q = 0.0
        two_pi_t_over_X = 2.0 * math.pi * t / X
        inv_pi_t = inv_pi / float(t)
        for q in range(1, q_small + 1):
            cq = ramanujan_sum(q, t, mu, phi)
            if cq:
                s_small_over_q += cq / q
                w_small += cq * math.sin(two_pi_t_over_X / q) * inv_pi_t
        # large-q linear
        s_large_over_q = S_all[t] - s_small_over_q
        w = w_small + scale_lin * s_large_over_q

        aw = abs(w)
        if aw > max_abs:
            max_abs = aw
            max_t = t

        w2 = w * w
        if t & 1:
            sum_sq_odd += w2
        else:
            sum_sq_even += w2
    t5 = time.perf_counter()
    print(f"[time] computed sums over t≤N0: {t5 - t4:.3f}s")

    print("\n== Band sums ==")
    print(f"sum_even |W_mix|^2: {sum_sq_even:.12e}")
    print(f"sum_odd  |W_mix|^2: {sum_sq_odd:.12e}")
    print(f"sum_all  |W_mix|^2: {(sum_sq_even + sum_sq_odd):.12e}")
    print(f"BW_mix (k=0 progression) = 2*sum_even: {(2.0 * sum_sq_even):.12e}")
    print(f"max |W_mix|: {max_abs:.6e} at t={max_t}")


if __name__ == "__main__":
    main()

