#!/usr/bin/env python3
"""
Experiment: compare the true hard-arc kernel W_hat(t) to the hybrid approximation

  W_mix(t) = W_small(t) + W_large_lin(t),

where:
  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(qX))   (t>0)
  W_small(t) = (1/(π t)) * Σ_{1≤q≤q_small} c_q(t) * sin(2π t/(qX))
  W_large_lin(t) = (2/X) * Σ_{q_small<q≤Q0} c_q(t)/q

and Σ_{q≤Q0} c_q(t)/q is computed *exactly* via the divisor-convolution identity:

  Σ_{q≤Q0} c_q(t)/q = Σ_{d|t, d≤Q0} ( Σ_{m≤Q0/d} μ(m)/m ).

This script samples t (optionally restricting parity) and reports moments of:
  - |W_hat(t)|, |W_mix(t)|, |W_hat(t)-W_mix(t)|.

Purpose:
  - quantify how close the hybrid model is to the true hard-arc kernel on the actual TT* bandwidth,
  - guide what size of rigorous remainder bound would be needed in a future certificate proof.

This is NOT a proof and does NOT generate a Lean certificate.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
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


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def build_S_all(*, Q0: int, Tmax: int, mu: list[int]) -> array:
    """
    Build S_all[t] := Σ_{q≤Q0} c_q(t)/q for 1≤t≤Tmax using the divisor-add identity.
    """
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


def w_hat_true(*, X: int, Q0: int, t: int, q_lo: int, q_hi: int, mu: list[int], phi: list[int]) -> float:
    """
    Compute (1/(π t)) * Σ_{q_lo≤q≤q_hi} c_q(t) * sin(2π t/(qX)).
    """
    s = 0.0
    two_pi_t_over_X = 2.0 * math.pi * t / X
    inv_pi_t = 1.0 / (math.pi * t)
    for q in range(q_lo, q_hi + 1):
        cq = ramanujan_sum(q, t, mu, phi)
        if cq:
            s += cq * math.sin(two_pi_t_over_X / q)
    return s * inv_pi_t


def main() -> None:
    ap = argparse.ArgumentParser(description="Experiment: W_hat(t) vs W_mix(t) remainder moments.")
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--Q0", type=int, default=30_000)
    ap.add_argument("--Tmax", type=int, default=1_010_000, help="Sample t in [1,Tmax].")
    ap.add_argument("--q-small", type=int, default=12)
    ap.add_argument("--samples", type=int, default=400)
    ap.add_argument("--seed", type=int, default=5)
    ap.add_argument("--parity", choices=["any", "even", "odd"], default="even")
    args = ap.parse_args()

    X = args.X
    Q0 = args.Q0
    Tmax = args.Tmax
    q_small = args.q_small
    if not (1 <= q_small < Q0):
        raise SystemExit("--q-small must satisfy 1 ≤ q_small < Q0")
    if X <= 0 or Q0 <= 0 or Tmax <= 0 or args.samples <= 0:
        raise SystemExit("Require positive parameters.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  Tmax={Tmax:,}  q_small={q_small}  samples={args.samples}  parity={args.parity}")

    t0 = time.perf_counter()
    mu = mobius_sieve(Q0)
    phi = totients_up_to(Q0)
    t1 = time.perf_counter()
    print(f"[time] sieve(mu,phi): {t1 - t0:.3f}s")

    t2 = time.perf_counter()
    S_all = build_S_all(Q0=Q0, Tmax=Tmax, mu=mu)
    t3 = time.perf_counter()
    print(f"[time] build S_all(t)=Σ c_q(t)/q: {t3 - t2:.3f}s")

    rng = random.Random(args.seed)

    def sample_t() -> int:
        while True:
            t = rng.randrange(1, Tmax + 1)
            if args.parity == "even" and (t & 1):
                continue
            if args.parity == "odd" and ((t & 1) == 0):
                continue
            return t

    abs_true: list[float] = []
    abs_mix: list[float] = []
    abs_rem: list[float] = []
    sq_true: list[float] = []
    sq_mix: list[float] = []
    sq_rem: list[float] = []
    max_abs_rem = 0.0
    max_t_rem = 1

    scale_lin = 2.0 / float(X)

    t4 = time.perf_counter()
    for _ in range(args.samples):
        t = sample_t()
        # Exact true W_hat over all q.
        w_true = w_hat_true(X=X, Q0=Q0, t=t, q_lo=1, q_hi=Q0, mu=mu, phi=phi)

        # Small-q exact part and also compute Σ_{q≤q_small} c_q(t)/q for subtracting from S_all.
        w_small = w_hat_true(X=X, Q0=Q0, t=t, q_lo=1, q_hi=q_small, mu=mu, phi=phi)
        s_small_over_q = 0.0
        for q in range(1, q_small + 1):
            cq = ramanujan_sum(q, t, mu, phi)
            if cq:
                s_small_over_q += cq / q
        s_large_over_q = S_all[t] - s_small_over_q
        w_large_lin = scale_lin * s_large_over_q
        w_mix = w_small + w_large_lin

        w_rem = w_true - w_mix

        at = abs(w_true)
        am = abs(w_mix)
        ar = abs(w_rem)
        if ar > max_abs_rem:
            max_abs_rem = ar
            max_t_rem = t

        abs_true.append(at)
        abs_mix.append(am)
        abs_rem.append(ar)
        sq_true.append(at * at)
        sq_mix.append(am * am)
        sq_rem.append(ar * ar)
    t5 = time.perf_counter()
    print(f"[time] computed {args.samples} samples: {t5 - t4:.3f}s")

    print("\n== Moments ==")
    print(f"max |rem|: {max_abs_rem:.6e} at t={max_t_rem}")
    print(f"mean |W_true|^2: {statistics.mean(sq_true):.6e}")
    print(f"mean |W_mix|^2:  {statistics.mean(sq_mix):.6e}")
    print(f"mean |rem|^2:    {statistics.mean(sq_rem):.6e}")
    print(f"mean |W_true|:   {statistics.mean(abs_true):.6e}")
    print(f"mean |W_mix|:    {statistics.mean(abs_mix):.6e}")
    print(f"mean |rem|:      {statistics.mean(abs_rem):.6e}")
    print(f"median |rem|:    {statistics.median(abs_rem):.6e}")

    # Extrapolated ℓ² mass on the full range 1..Tmax (heuristic).
    print("\n== Extrapolated full-range sums (heuristic) ==")
    print(f"Σ_{{t≤Tmax}} |rem(t)|^2 ≈ {Tmax * statistics.mean(sq_rem):.6e}")


if __name__ == "__main__":
    main()

