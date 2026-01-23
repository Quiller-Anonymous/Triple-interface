#!/usr/bin/env python3
from __future__ import annotations

"""
Experiment: "best plausible diagonal-only" TT* upper bound, keeping as much exactness as possible
without any q-dispersion lemma.

We compute:
  S2_exact := ∑_{n≤N0} Λ(n)^2 = ∑_{p^k ≤ N0} (log p)^2.

For the hard-arc Fourier coefficients (disjoint arcs), for t≠0:
  Ŵ_{X,q}(t) = c_q(t) * sin(2π t/(qX)) / (π t)
and Ŵ_{X,q}(0) = φ(q) * (2/(qX)).

Then for each q, define the square-sum:
  Bq2(q) := ∑_{|t|≤Tt} |Ŵ_{X0,q}(t)|^2.

Key tightening:
  For q ≥ 13, we have 2π*Tt/(qX0) < 1, so |sin y| ≤ y always and
    |Ŵ_{X0,q}(t)| ≤ 2*|c_q(t)|/(qX0)   for every 1≤|t|≤Tt,
  giving an exact-by-divisor-sums expression:
    Bq2(q) = (2φ(q)/(qX0))^2 + 8/(q^2 X0^2) * ∑_{t=1..Tt} |c_q(t)|^2.

For q ≤ 12, we compute Bq2(q) directly by summing t=1..Tt with the exact sin factor.

This is still "diagonal in q" (no cross-term cancellation); it is intended as an experimental
benchmark for how close diagonal-only could ever get to M2=50_000.
"""

from dataclasses import dataclass
from math import log, pi, sin
from typing import List


@dataclass(frozen=True)
class Params:
    Q0: int = 30_000
    X0: int = 1_000_000
    H: int = 10_000
    q_exact_max: int = 12


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


def sieve_primes(n: int) -> List[int]:
    is_prime = bytearray(b"\x01") * (n + 1)
    is_prime[0:2] = b"\x00\x00"
    for p in range(2, int(n**0.5) + 1):
        if is_prime[p]:
            step = p
            start = p * p
            is_prime[start : n + 1 : step] = b"\x00" * (((n - start) // step) + 1)
    return [i for i in range(n + 1) if is_prime[i]]


def S2_exact(N: int) -> float:
    primes = sieve_primes(N)
    total = 0.0
    for p in primes:
        lp = log(p)
        lp2 = lp * lp
        pk = p
        while pk <= N:
            total += lp2
            if pk > N // p:
                break
            pk *= p
    return total


def count_coprime_upto(mu: List[int], divs: List[List[int]], M: int, m: int) -> int:
    # #{u ≤ M : gcd(u,m)=1} = ∑_{e|m} μ(e) * floor(M/e)
    if M <= 0:
        return 0
    total = 0
    for e in divs[m]:
        total += mu[e] * (M // e)
    return total


def sum_cq_sq_upto(mu: List[int], phi: List[int], divs: List[List[int]], q: int, K: int) -> int:
    # ∑_{t=1..K} |c_q(t)|^2 with c_q(t)=μ(q/d)φ(d), d=gcd(q,t)
    total = 0
    for d in divs[q]:
        m = q // d
        mu2 = mu[m] * mu[m]
        if mu2 == 0:
            continue
        cnt = count_coprime_upto(mu, divs, K // d, m)
        total += mu2 * (phi[d] * phi[d]) * cnt
    return total


def cq_abs(mu: List[int], phi: List[int], q: int, t: int) -> int:
    # |c_q(t)| = μ(q/d)^2 * φ(d) where d=gcd(q,t).
    # We return |c_q(t)| (nonnegative integer).
    # compute d via Euclid
    a, b = q, t
    while b:
        a, b = b, a % b
    d = a
    m = q // d
    if mu[m] == 0:
        return 0
    return phi[d]


def main() -> None:
    p = Params()
    N0 = p.X0 + p.H
    Tt = 2 * N0
    print(f"Params: Q0={p.Q0}, X0={p.X0}, H={p.H}, N0={N0}, Tt={Tt}")

    print("Computing S2_exact = ∑_{n≤N0} Λ(n)^2 ...")
    s2 = S2_exact(N0)
    print(f"S2_exact ≈ {s2:.6e}")
    s2sq = s2 * s2
    print(f"S2_exact^2 ≈ {s2sq:.6e}")

    print("Precomputing mu, phi, divisors...")
    mu = mobius_up_to(p.Q0)
    phi = totients_up_to(p.Q0)
    divs = divisors_up_to(p.Q0)

    total_Bq2 = 0.0

    # q ≤ 12: direct t-sum with exact sin factor.
    for q in range(1, p.q_exact_max + 1):
        # t=0 contribution
        w0 = 2.0 * float(phi[q]) / (q * p.X0)
        acc = w0 * w0
        for t in range(1, Tt + 1):
            cq = cq_abs(mu, phi, q, t)
            if cq == 0:
                continue
            y = 2.0 * pi * t / (q * p.X0)
            wt = float(cq) * sin(y) / (pi * t)
            acc += 2.0 * (wt * wt)
        total_Bq2 += acc
        print(f"q={q:2d}: Bq2_exact ≈ {acc:.6e}")

    # q > 12: use |sin y| ≤ y (and y<1 holds for q≥13), giving Ŵ ≤ 2|c|/(qX).
    X0sq = float(p.X0 * p.X0)
    for q in range(p.q_exact_max + 1, p.Q0 + 1):
        w0 = 2.0 * float(phi[q]) / (q * p.X0)
        base = w0 * w0
        Sc2 = float(sum_cq_sq_upto(mu, phi, divs, q, Tt))
        acc = base + (8.0 / (q * q * X0sq)) * Sc2
        total_Bq2 += acc

    print(f"Σ_{'{q≤Q0}'} Bq2 (hybrid exact) ≈ {total_Bq2:.6e}")

    U_diag = s2sq * total_Bq2
    print(f"U_diag_best ≈ {U_diag:.6e}")

    M2sq = 50_000 * 50_000
    print(f"M2^2 = {M2sq}")
    print(f"Pass? {U_diag <= M2sq}")
    print(f"Ratio U_diag_best / M2^2 ≈ {U_diag/float(M2sq):.6e}")


if __name__ == '__main__':
    main()

