#!/usr/bin/env python3
from __future__ import annotations

"""
Compute the fully explicit (but very conservative) ε₂-large TT* upper bound U_expr
described in `Goldbach/Cert/MajorArcModules/STEP5_U_SPEC.md`.

This is the first generator-computable scaffold: it removes the `max_k` by a k-independent
envelope and uses only gcd/totient + a `min` split.

Important:
- This is NOT expected to pass the pinned budget `M2^2` yet.
- It is meant to be a stable baseline for successive tightening experiments.
"""

from dataclasses import dataclass
from math import log, log2
from typing import List, Tuple


@dataclass(frozen=True)
class Params:
    Q0: int = 30_000
    X0: int = 1_000_000
    H: int = 10_000
    # Rational upper bound for 1/pi (safe, crude).
    C_pi_inv: float = 1.0 / 3.0  # since 1/pi <= 1/3
    # Rational upper bound for log(N0+1) where N0 = X0+H.
    Lmax: int = 14


def dyadic_block_id(q: int) -> int:
    if q == 1:
        return 0
    return int(log2(q - 1)) + 1


def dyadic_block_count(Q0: int) -> int:
    if Q0 <= 1:
        return 1
    return int(log2(Q0 - 1)) + 2


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


def harmonic_numbers_up_to(n: int) -> List[Fraction]:
    raise RuntimeError("No longer used (was too slow for n≈2e6).")


def sum_gcd(phi: List[int], divs: List[List[int]], q: int, T: int) -> int:
    # ∑_{t=1..T} gcd(q,t) = ∑_{d|q} φ(d) * floor(T/d)
    total = 0
    for d in divs[q]:
        total += phi[d] * (T // d)
    return total


def sum_gcd_over_t(phi: List[int], divs: List[List[int]], H: List[Fraction], q: int, T: int) -> Fraction:
    raise RuntimeError("No longer used (we use a harmonic upper bound instead).")


def harmonic_upper(n: int) -> float:
    """
    Deterministic bound: H_n = ∑_{m=1..n} 1/m ≤ 1 + log n (for n≥1).
    """
    if n <= 0:
        return 0.0
    return 1.0 + log(float(n))


def sum_gcd_over_t_upper(phi: List[int], divs: List[List[int]], q: int, T: int) -> float:
    """
    Upper bound for ∑_{t=1..T} gcd(q,t)/t using:
      gcd(q,t) = ∑_{d|q, d|t} φ(d)
    and H_n ≤ 1 + log n.

    This is used only for q ≤ 12 in this scaffold (otherwise the min() picks the constant branch).
    """
    total = 0.0
    for d in divs[q]:
        total += (phi[d] / d) * harmonic_upper(T // d)
    return total


def compute_A_q(
    p: Params,
    phi: List[int],
    divs: List[List[int]],
    q: int,
    Tt: int,
) -> float:
    """
    A_q := B_q(0) + 2 * ∑_{t=1..Tt} gcd(q,t) * min( 2/(qX0), C_pi_inv/t ).

    B_q(0) := φ(q) * 2/(qX0).
    """
    A = 2.0 / (q * p.X0)
    B = p.C_pi_inv
    # threshold where B/t crosses A: t0 = floor(B/A) = floor(B * q*X0 / 2)
    t0 = int((B / A))

    base0 = (phi[q] * A)

    if t0 >= Tt:
        s = sum_gcd(phi, divs, q, Tt)
        return base0 + 2.0 * A * s

    # split at t0: A part + B/t tail
    s1 = sum_gcd(phi, divs, q, t0)
    tail = sum_gcd_over_t_upper(phi, divs, q, Tt) - sum_gcd_over_t_upper(phi, divs, q, t0)
    return base0 + 2.0 * (A * s1 + B * tail)


def main() -> None:
    p = Params()
    N0 = p.X0 + p.H
    Tt = 2 * N0

    print(f"Params: Q0={p.Q0}, X0={p.X0}, H={p.H}, N0={N0}, Tt={Tt}")
    print(f"Using C_pi_inv={p.C_pi_inv:.6g} (i.e. 1/pi <= 1/3), Lmax={p.Lmax}")

    print("Precomputing phi(q) and divisors(q)...")
    phi = totients_up_to(p.Q0)
    divs = divisors_up_to(p.Q0)

    Bcount = dyadic_block_count(p.Q0)
    block_sizes = [0] * Bcount
    q_by_block: List[List[int]] = [[] for _ in range(Bcount)]
    for q in range(1, p.Q0 + 1):
        j = dyadic_block_id(q)
        block_sizes[j] += 1
        q_by_block[j].append(q)

    print(f"Dyadic blocks: B={Bcount}, sizes (first 10)={block_sizes[:10]}")

    # Constant prefactor: B * (#kSupport(N0)) * (Lmax^4)
    ksupport_card = 2 * N0 + 1
    L4 = p.Lmax ** 4
    prefactor = float(Bcount * ksupport_card * L4)

    # Sum over blocks: ∑_j b_j ∑_{q in block(j)} A_q^2
    total = 0.0
    # Keep a crude “top blocks” breakdown for guidance.
    block_contrib: List[Tuple[int, float]] = []

    for j in range(Bcount):
        bj = block_sizes[j]
        if bj == 0:
            continue
        inner = 0.0
        for q in q_by_block[j]:
            Aq = compute_A_q(p, phi, divs, q, Tt)
            inner += Aq * Aq
        contrib = float(bj) * inner
        total += contrib
        block_contrib.append((j, contrib))

    U_expr = prefactor * total

    # Print results
    block_contrib.sort(key=lambda x: x[1], reverse=True)
    print("Top 10 block contributions to Σ_j b_j Σ_{q∈block(j)} A_q^2:")
    for j, c in block_contrib[:10]:
        print(f"  block {j:2d}: size={block_sizes[j]:5d}, contrib≈{c:.6e}")

    print(f"U_expr ≈ {U_expr:.6e}")

    M2 = 50_000
    M2sq = M2 * M2
    print(f"Budget check (informal, float): U_expr <= M2^2 ? {U_expr <= M2sq}")
    print(f"M2^2 = {M2sq}")


if __name__ == "__main__":
    main()
