#!/usr/bin/env python3
from __future__ import annotations

"""
ε₂-large TT*/Toeplitz tightening experiment (still "no dispersion"):

We keep the same L2 scaffold as exp_q0_u_expr_l2_scaffold.py, but tighten the
kernel square-sum bound by using the exact Ramanujan-sum size formula

  c_q(t) = μ(q/d) * φ(d),  where d = gcd(q,t),
so |c_q(t)|^2 = μ(q/d)^2 * φ(d)^2.

For the hard major arcs, disjointness gives the exact (t≠0) Fourier coefficient:
  Ŵ_{X,q}(t) = c_q(t) * sin(2π t/(qX)) / (π t)
and we upper bound |sin y| ≤ min(|y|,1) and 1/π ≤ 1/3.

This script computes a fully explicit upper bound for
  Bq2(q) := ∑_{|t|≤T} |Ŵ_{X0,q}(t)|^2
using divisor sums, and then forms:
  U_diag := S2^2 * Σ_q Bq2(q)          (ideal "diagonal in q" size)
  U_qcs  := Q0 * S2^2 * Σ_q Bq2(q)    (global C–S in q; current proved scaffold)

The point is to quantify how far we still are from M2^2=2.5e9 without any
q-dispersion lemma.
"""

from dataclasses import dataclass
from math import floor
from typing import List


@dataclass(frozen=True)
class Params:
    Q0: int = 30_000
    X0: int = 1_000_000
    H: int = 10_000
    # Rational inequality 1/pi <= 1/3.
    C_pi_inv: float = 1.0 / 3.0
    # Deterministic bound log(N0+1) <= 14 for N0=X0+H.
    L_log: int = 14


def mobius_up_to(n: int) -> List[int]:
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


def totients_up_to(n: int) -> List[int]:
    phi = list(range(n + 1))
    for p in range(2, n + 1):
        if phi[p] == p:
            for k in range(p, n + 1, p):
                phi[k] -= phi[k] // p
    return phi


def divisors_up_to(n: int) -> List[List[int]]:
    divs: List[List[int]] = [[] for _ in range(n + 1)]
    for d in range(1, n + 1):
        for k in range(d, n + 1, d):
            divs[k].append(d)
    return divs


def count_coprime_upto(mu: List[int], divs: List[List[int]], M: int, m: int) -> int:
    # #{u ≤ M : gcd(u,m)=1} = ∑_{e|m} μ(e) * floor(M/e)
    if M <= 0:
        return 0
    total = 0
    for e in divs[m]:
        total += mu[e] * (M // e)
    return total


def sum_cq_sq_upto(mu: List[int], phi: List[int], divs: List[List[int]], q: int, K: int) -> int:
    # ∑_{t=1..K} |c_q(t)|^2
    # = ∑_{d|q} μ(q/d)^2 * φ(d)^2 * #{u ≤ K/d : gcd(u, q/d)=1}
    total = 0
    for d in divs[q]:
        m = q // d
        mu2 = mu[m] * mu[m]
        if mu2 == 0:
            continue
        cnt = count_coprime_upto(mu, divs, K // d, m)
        total += mu2 * (phi[d] * phi[d]) * cnt
    return total


def tail_cq_sq_over_t2_bound(mu: List[int], phi: List[int], divs: List[List[int]], q: int, K: int) -> float:
    # Bound ∑_{t>K} |c_q(t)|^2 / t^2
    # Write t = d*u with d|q and gcd(u, q/d)=1, so |c_q(t)|^2 = μ(q/d)^2 φ(d)^2.
    # Then term = μ(q/d)^2 φ(d)^2 / (d^2 u^2). Summing u> K/d:
    #   ≤ μ(q/d)^2 φ(d)^2 / d^2 * (1/(K/d)) = μ(q/d)^2 φ(d)^2 / (d*K).
    if K <= 0:
        return 0.0
    total = 0.0
    for d in divs[q]:
        m = q // d
        mu2 = mu[m] * mu[m]
        if mu2 == 0:
            continue
        total += float(mu2) * float(phi[d] * phi[d]) / float(d * K)
    return total


def main() -> None:
    p = Params()
    N0 = p.X0 + p.H
    Tt = 2 * N0
    print(f"Params: Q0={p.Q0}, X0={p.X0}, H={p.H}, N0={N0}, Tt={Tt}")

    print("Precomputing mu, phi, and divisors...")
    mu = mobius_up_to(p.Q0)
    phi = totients_up_to(p.Q0)
    divs = divisors_up_to(p.Q0)

    # S2 := ∑_{n≤N0} Λ(n)^2 ≤ (log N0) * θ(N0) ≤ (log N0) * N0.
    S2 = float(p.L_log * N0)
    S2sq = S2 * S2
    print(f"S2_upper = {S2:.6e}, S2^2 = {S2sq:.6e}")

    B = p.C_pi_inv
    X0sq = float(p.X0 * p.X0)

    total_Bq2 = 0.0
    max_Bq2 = 0.0
    argmax_q = 1

    for q in range(1, p.Q0 + 1):
        # Bound |sin y| ≤ min(|y|,1).
        # For t≠0: |Ŵ_{q}(t)| ≤ |c_q(t)| * min(2/(qX0), B/|t|).
        A = 2.0 / (q * p.X0)
        # Switching threshold t0 = floor(B/A) = floor(B*q*X0/2) = floor(qX0/6).
        t0 = int(floor((B * q * p.X0) / 2.0))
        if t0 <= 0:
            t0 = 1
        K = min(t0, Tt)

        # head: t<=K uses min=A
        # 2 * A^2 * ∑_{t=1..K} |c_q(t)|^2
        Sq = float(sum_cq_sq_upto(mu, phi, divs, q, K))
        head = 2.0 * (A * A) * Sq

        # tail: t>K uses min=B/t
        # 2 * B^2 * ∑_{t=K+1..Tt} |c_q(t)|^2 / t^2
        tail = 0.0
        if K < Tt:
            tail = 2.0 * (B * B) * tail_cq_sq_over_t2_bound(mu, phi, divs, q, K)

        # t=0 term: |Ŵ_q(0)| ≤ φ(q)*2/(qX0)
        t0_term = (2.0 * float(phi[q]) / (q * p.X0)) ** 2

        Bq2 = t0_term + head + tail
        total_Bq2 += Bq2

        if Bq2 > max_Bq2:
            max_Bq2 = Bq2
            argmax_q = q

    print(f"Σ_{'{q≤Q0}'} Bq2(q) ≈ {total_Bq2:.6e}")
    print(f"max_q Bq2(q) ≈ {max_Bq2:.6e} at q={argmax_q}")

    U_diag = S2sq * total_Bq2
    U_qcs = float(p.Q0) * U_diag
    print(f"U_diag (no q factor) ≈ {U_diag:.6e}")
    print(f"U_qcs (global C–S in q) ≈ {U_qcs:.6e}")

    M2sq = 50_000 * 50_000
    print(f"M2^2 = {M2sq}")
    print(f"Pass diag? {U_diag <= M2sq}")
    print(f"Pass qcs?  {U_qcs <= M2sq}")

    # Required effective q-factor D (instead of Q0) to pass:
    if U_diag > 0:
        D_req = float(M2sq) / U_diag
        print(f"Required effective q-factor D ≤ {D_req:.6e} (vs Q0={p.Q0})")


if __name__ == '__main__':
    main()

