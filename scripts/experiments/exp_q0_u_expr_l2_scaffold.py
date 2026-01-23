#!/usr/bin/env python3
from __future__ import annotations

"""
Second tightening scaffold for ε₂-large TT*/Toeplitz:

Instead of bounding each |F_{k,q}| pointwise (which introduces a catastrophic |kSupport| factor),
we use:

  |F_{k,q}|^2 ≤ (∑_n |a_n a_{n+k}|^2) * (∑_n |Ŵ_{q}(2n+k-N)|^2)

and then sum over k:

  ∑_k |F_{k,q}|^2 ≤ (∑_n |a_n|^2)^2 * sup_k ∑_n |Ŵ_{q}(2n+k-N)|^2.

We upper bound the progression square-sum by the full t-range square-sum:

  sup_k ∑_n |Ŵ_q(2n+k-N)|^2 ≤ ∑_{t=-T..T} |Ŵ_q(t)|^2,  T = 2*(X0+H).

Then we combine q using global Cauchy–Schwarz in q:

  ∑_k |∑_q F_{k,q}|^2 ≤ Q0 * ∑_q ∑_k |F_{k,q}|^2.

This loses dispersion (no q,q' cancellation), but is dramatically tighter than the L1/max_k scaffold.
It is still fully explicit and uses only gcd/totient/divisor-sum bounds.
"""

from dataclasses import dataclass
from math import log2
from typing import List


@dataclass(frozen=True)
class Params:
    Q0: int = 30_000
    X0: int = 1_000_000
    H: int = 10_000
    # Use the rational inequality 1/pi <= 1/3 via C_pi_inv=1/3.
    C_pi_inv: float = 1.0 / 3.0
    # Deterministic bound log(N0+1) <= 14 for N0 = X0+H.
    L_log: int = 14


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


def sum_gcd(phi: List[int], divs: List[List[int]], q: int, T: int) -> int:
    # ∑_{t=1..T} gcd(q,t) = ∑_{d|q} φ(d) * floor(T/d)
    total = 0
    for d in divs[q]:
        total += phi[d] * (T // d)
    return total


def main() -> None:
    p = Params()
    N0 = p.X0 + p.H
    Tt = 2 * N0
    print(f"Params: Q0={p.Q0}, X0={p.X0}, H={p.H}, N0={N0}, Tt={Tt}")

    print("Precomputing phi(q) and divisors(q)...")
    phi = totients_up_to(p.Q0)
    divs = divisors_up_to(p.Q0)

    # S2 := ∑_{n≤N0} Λ(n)^2 ≤ (log N0) * θ(N0) ≤ (log N0) * N0.
    # With log N0 <= 14: S2 ≤ 14*N0.
    S2 = float(p.L_log * N0)
    S2sq = S2 * S2
    print(f"S2_upper = {S2:.6e}, S2^2 = {S2sq:.6e}")

    X0sq = float(p.X0 * p.X0)
    B = p.C_pi_inv

    total_Bq2 = 0.0
    max_Bq2 = 0.0
    argmax_q = 1

    # For q<12, the split point t0 = floor((B/A)) might be < Tt. For q>=12 it's >=Tt.
    for q in range(1, p.Q0 + 1):
        # A = 2/(qX0), t0 = floor(B/A) = floor(B*q*X0/2) = floor(qX0/6)
        t0 = int((B * q * p.X0) / 2.0)
        if t0 <= 0:
            t0 = 1
        if t0 >= Tt:
            t1 = Tt
        else:
            t1 = t0

        # head: t<=t1 uses min=A, with g^2 <= q*g.
        # Σ_{t=1..t1} q*g*(2/(qX0))^2 = Σ g * 4/(qX0^2)
        # include ±t: multiply by 2 -> 8/(qX0^2) * Σ_{t=1..t1} gcd(q,t)
        Sg = sum_gcd(phi, divs, q, t1)
        head = (8.0 / (q * X0sq)) * float(Sg)

        # tail: t>t1 uses min=B/t, with g^2 <= q*g
        # Σ_{t=t1+1..Tt} q*g*(B/t)^2 = q*B^2 Σ gcd(q,t)/t^2
        # include ±t: factor 2 -> 2*q*B^2 Σ gcd/t^2.
        # bound Σ_{t>t1} gcd(q,t)/t^2 ≤ τ(q)/t1.
        tau_q = float(len(divs[q]))
        tail = 0.0
        if t1 < Tt:
            tail = 2.0 * q * (B * B) * (tau_q / float(t1))

        # t=0 term: |Ŵ_q(0)| ≤ φ(q)*2/(qX0)
        t0_term = (2.0 * float(phi[q]) / (q * p.X0)) ** 2

        Bq2 = t0_term + head + tail
        total_Bq2 += Bq2

        if Bq2 > max_Bq2:
            max_Bq2 = Bq2
            argmax_q = q

    print(f"Σ_{'{q≤Q0}'} Bq2(q) ≈ {total_Bq2:.6e}")
    print(f"max_q Bq2(q) ≈ {max_Bq2:.6e} at q={argmax_q}")

    # Global C–S in q:
    # TT ≤ Q0 * (S2^2) * Σ_q Bq2(q)
    U = float(p.Q0) * S2sq * total_Bq2
    print(f"U_l2_scaffold ≈ {U:.6e}")

    M2sq = 50_000 * 50_000
    print(f"Budget check (float): U <= M2^2 ? {U <= M2sq}")
    print(f"M2^2 = {M2sq}")


if __name__ == "__main__":
    main()

