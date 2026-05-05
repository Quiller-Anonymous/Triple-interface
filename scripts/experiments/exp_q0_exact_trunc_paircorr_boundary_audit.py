#!/usr/bin/env python3
"""
Exact centered truncation audit on the direct downstream Route A surface.

This script computes, at fixed `X`:

  - exact diagonal truncation energy
  - exact total centered truncation window energy
  - exact off-diagonal pair-correlation sum
  - exact coefficient-supported periodic-main off-diagonal sum
  - exact boundary sum = pair-correlation sum - periodic-main sum

It works directly with the coefficient-supported truncation summands

  c(q) * ramanujanR(q,N)

centered by their even-window averages, so the pair-correlation total is exact and does not rely on
branch decompositions. The periodic-main part is computed exactly on the active full-block surface
(`2*lcm(q,q') <= H+1`), where only those pairs can contribute.
"""

from __future__ import annotations

import argparse
import math
from collections import defaultdict


H = 10_000
Q0 = 30_000
C2_NUMERIC = 0.1


def mobius_phi_sieve(n: int) -> tuple[list[int], list[int]]:
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


def spf_sieve(n: int) -> list[int]:
    spf = list(range(n + 1))
    if n >= 0:
        spf[0] = 0
    if n >= 1:
        spf[1] = 1
    for i in range(2, int(math.isqrt(n)) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def primes_from_spf(spf: list[int]) -> list[int]:
    return [n for n in range(2, len(spf)) if spf[n] == n]


def factorization(n: int, spf: list[int]) -> dict[int, int]:
    out: dict[int, int] = {}
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out[p] = e
    return out


def divisors_from_factorization(fac: dict[int, int]) -> list[int]:
    divs = [1]
    for p, e in fac.items():
        cur: list[int] = []
        pe = 1
        for _ in range(e + 1):
            for d in divs:
                cur.append(d * pe)
            pe *= p
        divs = cur
    divs.sort()
    return divs


def totient_trial(n: int, primes: list[int]) -> int:
    if n == 0:
        raise ValueError("totient_trial expects positive input")
    result = n
    m = n
    for p in primes:
        if p * p > m:
            break
        if m % p == 0:
            while m % p == 0:
                m //= p
            result -= result // p
    if m > 1:
        result -= result // m
    return result


def coeff_support(Q: int, mu: list[int]) -> list[int]:
    return [q for q in range(1, Q + 1) if mu[q] != 0]


def even_window_points(X: int) -> list[int]:
    start = X if X % 2 == 0 else X + 1
    return list(range(start, X + H + 1, 2))


def normalized_sigma_trunc_summand_real_coeff(q: int, mu: list[int], phi: list[int]) -> float:
    if mu[q] == 0:
        return 0.0
    return 1.0 / (((phi[q]) ** 2) * (2.0 * C2_NUMERIC))


def ramanujan_sum(q: int, n: int, mu: list[int], phi: list[int]) -> int:
    g = math.gcd(q, n)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def ramanujan_gcd_class_coeff(q: int, g: int, mu: list[int], phi: list[int]) -> float:
    return float(mu[q // g] * phi[g])


def ceil_div(a: int, b: int) -> int:
    return (a + b - 1) // b


def block_period(q: int, q2: int) -> int:
    return 2 * math.lcm(q, q2)


def full_block_even_points(X: int, P: int) -> list[int]:
    return [X + k for k in range(P) if (X + k) % 2 == 0]


def count_coprime_shifted(start: int, modulus: int, length: int) -> int:
    return sum(1 for t in range(length) if math.gcd(modulus, start + t) == 1)


def main() -> None:
    ap = argparse.ArgumentParser(description="Exact truncation/periodic-main/boundary audit.")
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--q-max-active", type=int, default=(H + 1) // 2)
    args = ap.parse_args()

    X = args.X
    q_active_max = args.q_max_active

    mu, phi = mobius_phi_sieve(Q0)
    spf = spf_sieve(Q0)
    primes = primes_from_spf(spf)

    support = coeff_support(Q0, mu)
    active_support = [q for q in support if q <= q_active_max]
    even_window = even_window_points(X)
    even_window_card = len(even_window)

    coeff_q: dict[int, float] = {}
    diagonal = 0.0
    total_vec = [0.0] * even_window_card

    # Exact diagonal and total truncation observable on the full coefficient support.
    for q in support:
        c_q = normalized_sigma_trunc_summand_real_coeff(q, mu, phi)
        coeff_q[q] = c_q
        vals = [c_q * float(ramanujan_sum(q, N, mu, phi)) for N in even_window]
        avg = math.fsum(vals) / float(even_window_card)
        centered_vals = [v - avg for v in vals]
        diagonal += math.fsum(v * v for v in centered_vals)
        for i, v in enumerate(centered_vals):
            total_vec[i] += v

    total_window_energy = math.fsum(v * v for v in total_vec)
    pair_correlation_total = total_window_energy - diagonal

    # Exact periodic-main total on the active full-block coefficient-supported surface.
    divisors: dict[int, list[int]] = {}
    even_divisors: dict[int, list[int]] = {}
    gcd_coeff: dict[tuple[int, int], float] = {}
    averages: dict[int, dict[int, float]] = {}

    for q in active_support:
        fac = factorization(q, spf)
        divs = divisors_from_factorization(fac)
        divisors[q] = divs
        even_divisors[q] = [d for d in divs if d % 2 == 0]
        for g in divs:
            gcd_coeff[(q, g)] = ramanujan_gcd_class_coeff(q, g, mu, phi)
        counts: dict[int, int] = defaultdict(int)
        for N in even_window:
            counts[math.gcd(q, N)] += 1
        averages[q] = {g: counts.get(g, 0) / float(even_window_card) for g in divs}

    def pair_main(q: int, q2: int) -> float:
        P = block_period(q, q2)
        full_blocks = (H + 1) // P
        if full_blocks == 0:
            return 0.0

        even_block = P // 2
        Ns = full_block_even_points(X, P)

        left_counts: dict[int, int] = defaultdict(int)
        right_counts: dict[int, int] = defaultdict(int)
        pair_counts: dict[tuple[int, int], int] = defaultdict(int)
        for N in Ns:
            g = math.gcd(q, N)
            h = math.gcd(q2, N)
            left_counts[g] += 1
            right_counts[h] += 1
            pair_counts[(g, h)] += 1

        out = 0.0
        coeff_pair = coeff_q[q] * coeff_q[q2]
        for g in divisors[q]:
            avg_g = averages[q][g]
            left = float(left_counts.get(g, 0))
            c_g = gcd_coeff[(q, g)]
            for h in divisors[q2]:
                avg_h = averages[q2][h]
                right = float(right_counts.get(h, 0))
                pair = float(pair_counts.get((g, h), 0))
                c_h = gcd_coeff[(q2, h)]
                centered_full_block = pair - avg_h * left - avg_g * right + avg_g * avg_h * even_block
                out += coeff_pair * c_g * c_h * float(full_blocks) * centered_full_block
        return out

    periodic_main_total = 0.0
    active_main_unordered_pairs = 0
    for i, q in enumerate(active_support):
        for q2 in active_support[i + 1:]:
            val = pair_main(q, q2)
            if val == 0.0:
                continue
            active_main_unordered_pairs += 1
            periodic_main_total += 2.0 * val

    boundary_total = pair_correlation_total - periodic_main_total

    # Optional exact split of active periodic-main pairs by coprimality.
    periodic_main_coprime = 0.0
    periodic_main_noncoprime = 0.0
    for i, q in enumerate(active_support):
        for q2 in active_support[i + 1:]:
            val = pair_main(q, q2)
            if val == 0.0:
                continue
            if math.gcd(q, q2) == 1:
                periodic_main_coprime += 2.0 * val
            else:
                periodic_main_noncoprime += 2.0 * val

    print(f"X = {X}")
    print(f"even window card = {even_window_card}")
    print(f"coeff support card = {len(support)}")
    print(f"active periodic-main support cutoff = {q_active_max}")
    print(f"active periodic-main support card = {len(active_support)}")
    print(f"active periodic-main unordered offdiag pairs = {active_main_unordered_pairs}")
    print()
    print(f"diagonalExact              = {diagonal:.12f}")
    print(f"windowEnergyExact          = {total_window_energy:.12f}")
    print(f"pairCorrelationTotal       = {pair_correlation_total:.12f}")
    print(f"periodicMainTotal          = {periodic_main_total:.12f}")
    print(f"  periodicMainCoprime      = {periodic_main_coprime:.12f}")
    print(f"  periodicMainNonCoprime   = {periodic_main_noncoprime:.12f}")
    print(f"boundaryTotal              = {boundary_total:.12f}")
    if pair_correlation_total != 0.0:
        print(f"boundaryShareOfPairCorr    = {boundary_total / pair_correlation_total:.12f}")
    if total_window_energy != 0.0:
        print(f"diagonalShareOfEnergy      = {diagonal / total_window_energy:.12f}")
        print(f"offdiagShareOfEnergy       = {pair_correlation_total / total_window_energy:.12f}")


if __name__ == "__main__":
    main()
