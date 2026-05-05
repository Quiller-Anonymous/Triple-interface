#!/usr/bin/env python3
"""
Exact supported-Q0 periodic-main residual audit for Q0MinorZeroModeNormalizedAverage.

This mirrors only the explicit finite definitions needed for the residual diagnostic:

  supportedDiagonal
  supportedOffDiagonal
  commonPrime
  preferred gcd correction (via the exact gcd-correction term; equal on support)
  remainder

and then computes

  R_off   = supportedOffDiagonal - commonPrime - preferredGcd - remainder
  R_total = supportedNonCoprimeResidual - supportedDiagonal

with the identity check

  R_off = R_total.

It also widens the exact full-block periodic-main computation to the active coefficient support
(`Squarefree q` with `2*lcm(q,q') <= H+1`), so we can audit the exact downstream object

  centeredNormalizedSigmaTruncPeriodicMainRemainingPairSumUpToQ0

via

  coeff-supported off-diagonal periodic main - clean supported non-coprime defect.

The script intentionally works on the explicit finite definitions and does not use theorem-level
majorants.
"""

from __future__ import annotations

import argparse
import math
from collections import defaultdict
from typing import Dict


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


def is_even(n: int) -> bool:
    return (n % 2) == 0


def ord_compl_two_factorization(q: int, spf: list[int]) -> dict[int, int]:
    n = q
    while n % 2 == 0 and n > 0:
        n //= 2
    return factorization(n, spf)


def one_variable_support(q: int, spf: list[int]) -> bool:
    if not is_even(q):
        return False
    odd_fac = ord_compl_two_factorization(q, spf)
    return all(e >= 2 for e in odd_fac.values())


def normalized_sigma_trunc_summand_real_coeff(q: int, mu: list[int], phi: list[int]) -> float:
    if mu[q] == 0:
        return 0.0
    return 1.0 / (((phi[q]) ** 2) * (2.0 * C2_NUMERIC))


def ramanujan_gcd_class_coeff(q: int, g: int, mu: list[int], phi: list[int]) -> float:
    return float(mu[q // g] * phi[g])


def ceil_div(a: int, b: int) -> int:
    return (a + b - 1) // b


def block_period(q: int, q2: int) -> int:
    return 2 * math.lcm(q, q2)


def even_window_points(X: int) -> list[int]:
    start = X if is_even(X) else X + 1
    return list(range(start, X + H + 1, 2))


def full_block_even_points(X: int, P: int) -> list[int]:
    return [X + k for k in range(P) if is_even(X + k)]


def count_coprime_shifted(start: int, modulus: int, length: int) -> int:
    return sum(1 for t in range(length) if math.gcd(modulus, start + t) == 1)


def joint_compatibility(q: int, q2: int, g: int, h: int) -> bool:
    return (
        math.gcd(q // g, math.lcm(g, h) // g) == 1
        and math.gcd(q2 // h, math.lcm(g, h) // h) == 1
    )


def build_support(Q: int, spf: list[int]) -> list[int]:
    return [q for q in range(1, Q + 1) if one_variable_support(q, spf)]


def build_coeff_support(Q: int, mu: list[int]) -> list[int]:
    return [q for q in range(1, Q + 1) if mu[q] != 0]


def main() -> None:
    ap = argparse.ArgumentParser(description="Exact supported-Q0 periodic-main residual audit.")
    ap.add_argument("--X", type=int, default=100_000)
    ap.add_argument("--q-max-active", type=int, default=(H + 1) // 2, help="Only q <= this can contribute because (H+1)//(2*lcm(q,q')) must be nonzero.")
    args = ap.parse_args()

    X = args.X
    active_q_max = args.q_max_active

    mu, phi = mobius_phi_sieve(Q0)
    spf = spf_sieve(Q0)
    primes = primes_from_spf(spf)
    support = build_support(Q0, spf)
    active_support = [q for q in support if q <= active_q_max]
    coeff_support = build_coeff_support(Q0, mu)
    active_coeff_support = [q for q in coeff_support if q <= active_q_max]
    active_union = sorted(set(active_support) | set(active_coeff_support))

    even_window = even_window_points(X)
    even_window_card = len(even_window)

    divisors: dict[int, list[int]] = {}
    even_divisors: dict[int, list[int]] = {}
    coeff_q: dict[int, float] = {}
    gcd_coeff: dict[tuple[int, int], float] = {}
    averages: dict[int, dict[int, float]] = {}

    for q in active_union:
        fac = factorization(q, spf)
        divs = divisors_from_factorization(fac)
        divisors[q] = divs
        even_divisors[q] = [d for d in divs if is_even(d)]
        coeff_q[q] = normalized_sigma_trunc_summand_real_coeff(q, mu, phi)
        for g in divs:
            gcd_coeff[(q, g)] = ramanujan_gcd_class_coeff(q, g, mu, phi)

        counts: dict[int, int] = defaultdict(int)
        for N in even_window:
            counts[math.gcd(q, N)] += 1
        averages[q] = {g: counts.get(g, 0) / float(even_window_card) for g in divs}

    def pair_periodic_data(q: int, q2: int) -> tuple[float, float, float, float]:
        P = block_period(q, q2)
        full_blocks = (H + 1) // P
        if full_blocks == 0:
            return 0.0, 0.0, 0.0, 0.0

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

        pair_main = 0.0
        pair_common_prime = 0.0
        pair_gcd_correction = 0.0
        pair_remainder = 0.0

        coeff_pair = coeff_q[q] * coeff_q[q2]
        if coeff_pair != 0.0:
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
                    pair_main += coeff_pair * c_g * c_h * float(full_blocks) * centered_full_block

        for g in even_divisors[q]:
            c_g = gcd_coeff[(q, g)]
            for h in even_divisors[q2]:
                c_h = gcd_coeff[(q2, h)]
                A = q // g
                B = q2 // h
                d = math.gcd(A, B)
                lcm_gh = math.lcm(g, h)
                pair_start = ceil_div(X, lcm_gh)
                pair_len = ((X + P - 1) // lcm_gh + 1) - pair_start
                pair_rem = count_coprime_shifted(
                    pair_start + (pair_len // (A * B)) * (A * B),
                    A * B,
                    pair_len % (A * B),
                )

                left_start = ceil_div(X, g)
                left_len = ((X + P - 1) // g + 1) - left_start
                left_rem = count_coprime_shifted(
                    left_start + (left_len // A) * A,
                    A,
                    left_len % A,
                )

                right_start = ceil_div(X, h)
                right_len = ((X + P - 1) // h + 1) - right_start
                right_rem = count_coprime_shifted(
                    right_start + (right_len // B) * B,
                    B,
                    right_len % B,
                )

                common_prime_overlap = float(phi[A] * phi[B]) * float(pair_len // (A * B)) * (
                    (float(d) / float(phi[d])) - 1.0
                )
                coefficient_mismatch = float(phi[A] * phi[B]) * (
                    float(pair_len // (A * B))
                    - (float(left_len // A) * float(right_len // B)) / float(even_block)
                )
                totient_comparison = (
                    float((pair_len // (A * B)) * totient_trial(A * B, primes) + pair_rem)
                    - (
                        float((left_len // A) * phi[A] + left_rem)
                        * float((right_len // B) * phi[B] + right_rem)
                    ) / float(even_block)
                )
                remainder_term = totient_comparison - coefficient_mismatch - common_prime_overlap

                weight = c_g * c_h * float(full_blocks)
                pair_common_prime += weight * common_prime_overlap
                pair_gcd_correction += weight * coefficient_mismatch
                pair_remainder += weight * remainder_term

        return pair_main, pair_common_prime, pair_gcd_correction, pair_remainder

    supported_diagonal = 0.0
    supported_off_diagonal = 0.0
    common_prime_total = 0.0
    gcd_correction_total = 0.0
    remainder_total = 0.0

    active_pairs = 0
    for q in active_support:
        for q2 in active_support:
            pair_main, pair_common_prime, pair_gcd_correction, pair_remainder = pair_periodic_data(q, q2)
            if pair_main == 0.0 and pair_common_prime == 0.0 and pair_gcd_correction == 0.0 and pair_remainder == 0.0:
                continue
            active_pairs += 1

            if q == q2:
                supported_diagonal += pair_main
            else:
                supported_off_diagonal += pair_main

            common_prime_total += pair_common_prime
            gcd_correction_total += pair_gcd_correction
            remainder_total += pair_remainder

    coeff_supported_offdiag = 0.0
    coeff_supported_coprime_offdiag = 0.0
    coeff_supported_noncoprime_offdiag = 0.0
    coeff_active_offdiag_pairs = 0
    for i, q in enumerate(active_coeff_support):
        for q2 in active_coeff_support[i + 1:]:
            pair_main, _, _, _ = pair_periodic_data(q, q2)
            if pair_main == 0.0:
                continue
            coeff_active_offdiag_pairs += 2
            coeff_supported_offdiag += 2.0 * pair_main
            if math.gcd(q, q2) == 1:
                coeff_supported_coprime_offdiag += 2.0 * pair_main
            else:
                coeff_supported_noncoprime_offdiag += 2.0 * pair_main

    clean_total = common_prime_total + gcd_correction_total + remainder_total
    supported_main_total = supported_diagonal + supported_off_diagonal
    residual_total = supported_main_total - clean_total
    off_model_residual = supported_off_diagonal - clean_total
    validation_gap = off_model_residual - (residual_total - supported_diagonal)
    outside_support = coeff_supported_offdiag - supported_diagonal
    remaining_exact = coeff_supported_offdiag - clean_total
    remaining_via_split = residual_total + outside_support
    remaining_gap = remaining_exact - remaining_via_split

    print(f"X = {X}")
    print(f"support card = {len(support)}")
    print(f"support sum = {sum(support)}")
    print(f"active support cutoff = {active_q_max}")
    print(f"active support card = {len(active_support)}")
    print(f"active pair count = {active_pairs}")
    print(f"coeff support card = {len(coeff_support)}")
    print(f"active coeff support card = {len(active_coeff_support)}")
    print(f"active coeff offdiag ordered pairs = {coeff_active_offdiag_pairs}")
    print()
    print(f"supportedDiagonal           = {supported_diagonal:.12f}")
    print(f"supportedOffDiagonal        = {supported_off_diagonal:.12f}")
    print(f"commonPrime                 = {common_prime_total:.12f}")
    print(f"preferredGcdCorrection      = {gcd_correction_total:.12f}")
    print(f"remainder                   = {remainder_total:.12f}")
    print()
    print(f"supportedMainTotal          = {supported_main_total:.12f}")
    print(f"supportedNonCoprimeResidual = {residual_total:.12f}")
    print(f"supportedOffDiagModelResid  = {off_model_residual:.12f}")
    print(f"residualMinusDiagonal       = {residual_total - supported_diagonal:.12f}")
    print(f"validationGap               = {validation_gap:.12e}")
    print()
    print(f"coeffSupportedOffDiagonal   = {coeff_supported_offdiag:.12f}")
    print(f"coeffSupportedCoprime       = {coeff_supported_coprime_offdiag:.12f}")
    print(f"coeffSupportedNonCoprime    = {coeff_supported_noncoprime_offdiag:.12f}")
    print(f"outsideSupport              = {outside_support:.12f}")
    print(f"remainingExact              = {remaining_exact:.12f}")
    print(f"remainingViaResidualSplit   = {remaining_via_split:.12f}")
    print(f"remainingValidationGap      = {remaining_gap:.12e}")


if __name__ == "__main__":
    main()
