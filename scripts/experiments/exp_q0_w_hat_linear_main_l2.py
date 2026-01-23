#!/usr/bin/env python3
"""
Experiment: compute the ℓ² mass (over t up to Tmax) of the *linearized* hard-arc kernel.

Setup (pinned Step5 parameters by default):
  X = 1_000_000, Q0 = 30_000, Tmax = 2*X (or chosen).

For the hard arcs (disjoint regime, Δ=1), for t≠0:
  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(qX)).

When q is large relative to t (in practice q≥13 for t≤2*X0), we are in the small-angle regime:
  sin(2π t/(qX)) ≈ 2π t/(qX),
so the contribution becomes approximately:
  (1/(π t)) * c_q(t) * (2π t/(qX)) = (2/X) * c_q(t)/q.

Thus the "linear main term" is:
  W_lin(t) := (2/X) * Σ_{q≤Q0} c_q(t)/q.

Key identity (Ramanujan sum expansion):
  c_q(t) = Σ_{d | gcd(q,t)} μ(q/d) * d,
so
  Σ_{q≤Q0} c_q(t)/q = Σ_{d|t, d≤Q0} ( Σ_{m≤Q0/d} μ(m)/m ).

Let M(u) := Σ_{m≤u} μ(m)/m. Define A[d] := M(Q0/d).
Then S(t) := Σ_{q≤Q0} c_q(t)/q is the divisor convolution:
  S(t) = Σ_{d|t, d≤Q0} A[d].

We can compute S(t) for all 1≤t≤Tmax in O(Tmax log Q0) time by
adding A[d] to all multiples of d.

Outputs:
  - Σ_{1≤t≤Tmax} |W_lin(t)|^2 (and even/odd splits),
  - mean |W_lin(t)|^2 over t,
  - max |W_lin(t)| over t in range.

This is NOT a proof and does NOT generate a Lean certificate; it is intended to guide
which dispersion/linearization inequality is promising for "U tightening".
"""

from __future__ import annotations

import argparse
import math
import time
from array import array


def mobius_sieve(n: int) -> list[int]:
    """Compute μ(0..n) via a linear-ish sieve (sufficient for n=30k)."""
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


def prefix_mertens_over_m(mu: list[int]) -> array:
    """
    Return prefix sums M[k] = Σ_{m≤k} μ(m)/m as double-precision floats.
    """
    n = len(mu) - 1
    M = array("d", [0.0]) * (n + 1)
    acc = 0.0
    for m in range(1, n + 1):
        acc += float(mu[m]) / float(m)
        M[m] = acc
    return M


def main() -> None:
    ap = argparse.ArgumentParser(description="Experiment: ℓ² mass of W_lin(t) (linearized hard-arc kernel).")
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--Q0", type=int, default=30_000)
    ap.add_argument("--Tmax", type=int, default=None, help="Compute over 1..Tmax; default 2*X.")
    args = ap.parse_args()

    X = args.X
    Q0 = args.Q0
    Tmax = (2 * X) if args.Tmax is None else args.Tmax
    if X <= 0 or Q0 <= 0 or Tmax <= 0:
        raise SystemExit("Require X,Q0,Tmax positive.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  Tmax={Tmax:,}")

    t0 = time.perf_counter()
    mu = mobius_sieve(Q0)
    t1 = time.perf_counter()
    M = prefix_mertens_over_m(mu)
    t2 = time.perf_counter()
    print(f"[time] sieve(mu): {t1 - t0:.3f}s")
    print(f"[time] prefix M(u)=Σ μ(m)/m: {t2 - t1:.3f}s")

    # A[d] := M[Q0//d]
    A = array("d", [0.0]) * (Q0 + 1)
    for d in range(1, Q0 + 1):
        A[d] = M[Q0 // d]

    # Compute S[t] := Σ_{d|t, d≤Q0} A[d] for 1≤t≤Tmax by multiples.
    S = array("d", [0.0]) * (Tmax + 1)
    t3 = time.perf_counter()
    for d in range(1, Q0 + 1):
        ad = A[d]
        for t in range(d, Tmax + 1, d):
            S[t] += ad
    t4 = time.perf_counter()
    print(f"[time] filled S(t) by divisor-add: {t4 - t3:.3f}s")

    # W_lin(t) = (2/X) * S(t)
    scale = 2.0 / float(X)
    sum_sq_all = 0.0
    sum_sq_even = 0.0
    sum_sq_odd = 0.0
    max_abs = 0.0
    max_t = 1
    t5 = time.perf_counter()
    for t in range(1, Tmax + 1):
        w = scale * S[t]
        aw = abs(w)
        if aw > max_abs:
            max_abs = aw
            max_t = t
        w2 = w * w
        sum_sq_all += w2
        if (t & 1) == 0:
            sum_sq_even += w2
        else:
            sum_sq_odd += w2
    t6 = time.perf_counter()
    print(f"[time] accumulated ℓ² stats: {t6 - t5:.3f}s")

    mean_sq_all = sum_sq_all / float(Tmax)
    mean_sq_even = sum_sq_even / float(Tmax // 2)
    mean_sq_odd = sum_sq_odd / float((Tmax + 1) // 2)

    print("\n== Results for W_lin(t) = (2/X) * Σ_{q≤Q0} c_q(t)/q ==")
    print(f"max |W_lin|: {max_abs:.6e} at t={max_t}")
    print(f"mean |W_lin|^2 (all):  {mean_sq_all:.6e}")
    print(f"sum  |W_lin|^2 (all):  {sum_sq_all:.6e}")
    print(f"mean |W_lin|^2 (even): {mean_sq_even:.6e}")
    print(f"sum  |W_lin|^2 (even): {sum_sq_even:.6e}")
    print(f"mean |W_lin|^2 (odd):  {mean_sq_odd:.6e}")
    print(f"sum  |W_lin|^2 (odd):  {sum_sq_odd:.6e}")


if __name__ == "__main__":
    main()

