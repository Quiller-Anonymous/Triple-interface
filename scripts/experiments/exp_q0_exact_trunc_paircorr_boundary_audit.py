#!/usr/bin/env python3
"""
Centered truncation audit on the direct downstream Route A surface.

This script computes, at fixed `X`, the direct downstream truncation profile for either:

  - the numeric surrogate normalization `C2_numeric = 1/10`, or
  - a numerical approximation to the true Lean normalization `ramanujanSeriesOnWindow.C.C2`.

For the chosen normalization it computes:

  - diagonal truncation energy
  - total centered truncation window energy
  - off-diagonal pair-correlation sum
  - coefficient-supported periodic-main off-diagonal sum
  - boundary sum = pair-correlation sum - periodic-main sum

It works directly with the coefficient-supported truncation summands

  c(q) * ramanujanR(q,N)

centered by their even-window averages, so the pair-correlation total is exact and does not rely
on branch decompositions. The periodic-main part is computed exactly on the active full-block
surface (`2*lcm(q,q') <= H+1`), where only those pairs can contribute.

For `--true-series`, the only numerical approximation is the value of the true Euler-product
constant `C2_true`. Once that constant is fixed, the direct downstream quantities scale exactly by
the square of the coefficient ratio, because every centered summand is linear in `1 / (2*C2)`.
"""

from __future__ import annotations

import argparse
import contextlib
import heapq
import json
import math
import multiprocessing
import os
import sys
import time
from collections import Counter, defaultdict
from decimal import Decimal
from fractions import Fraction


H = 10_000
Q0 = 30_000
C2_NUMERIC = 0.1
DIAG_MAIN_LOW_Q = {3, 5, 6, 7, 10, 14}


_BOUNDARY_EXACT_PARALLEL_GLOBALS: dict[str, object] = {}
_PERIODIC_MAIN_EXACT_PARALLEL_GLOBALS: dict[str, object] = {}


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


def prime_sieve(n: int) -> list[int]:
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(math.isqrt(n)) + 1):
        if sieve[p]:
            start = p * p
            step = p
            sieve[start:n + 1:step] = b"\x00" * (((n - start) // step) + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def true_c2_from_odd_prime_euler_product(prime_cutoff: int) -> tuple[float, float]:
    """
    Numerical approximation to the true Lean-side `C2` using the classical odd-prime Euler product

        C2_true = ∏_{p odd prime} (1 - 1/(p-1)^2).

    This matches the realized Ramanujan series constant because for powers of two the odd-prime
    support is empty, so `sigma(2) = 2*C2_true`, while the true series object agrees with the full
    Ramanujan series on the window.

    Returns:
      (product approximation, crude absolute error bound)

    The error bound is derived from
      log(C2_true / C2_cutoff) <= Σ_{p>y} a_p/(1-a_p),  a_p = 1/(p-1)^2 <= 1/4,
    and the coarse estimate
      Σ_{p>y} 1/(p-1)^2 <= Σ_{n>y} 1/(n-1)^2 <= 1/(y-1).
    """
    if prime_cutoff < 3:
        raise ValueError("prime_cutoff must be at least 3")

    product = 1.0
    for p in prime_sieve(prime_cutoff):
        if p == 2:
            continue
        product *= 1.0 - 1.0 / float((p - 1) ** 2)

    tail_log_upper = 4.0 / (3.0 * float(prime_cutoff - 1))
    abs_error_upper = product * math.expm1(tail_log_upper)
    return product, abs_error_upper


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


def sum_abs_ramanujan_gcd_class_coeff(q: int, mu: list[int], phi: list[int], spf: list[int]) -> int:
    fac_q = factorization(q, spf)
    return sum(abs(mu[q // g] * phi[g]) for g in divisors_from_factorization(fac_q))


def ceil_div(a: int, b: int) -> int:
    return (a + b - 1) // b


def block_period(q: int, q2: int) -> int:
    return 2 * math.lcm(q, q2)


def full_block_even_points(X: int, P: int) -> list[int]:
    return [X + k for k in range(P) if (X + k) % 2 == 0]


def full_block_even_progression(X: int, P: int) -> tuple[int, int]:
    first_even = X if X % 2 == 0 else X + 1
    return first_even, P // 2


def boundary_remainder_even_count(X: int, q: int, q2: int) -> int:
    P = block_period(q, q2)
    m = (H + 1) // P
    r = (H + 1) % P
    return sum(1 for k in range(r) if (X + m * P + k) % 2 == 0)


def boundary_remainder_even_progression(X: int, q: int, q2: int) -> tuple[int, int]:
    """
    Return `(first_even, even_count)` for the boundary remainder progression.

    The even boundary points are exactly

      first_even, first_even + 2, ..., first_even + 2*(even_count-1)

    inside the short remainder interval after the full periodic blocks.
    """
    P = block_period(q, q2)
    m = (H + 1) // P
    r = (H + 1) % P
    start0 = X + m * P
    stop0 = start0 + r
    first_even = start0 if start0 % 2 == 0 else start0 + 1
    if first_even >= stop0:
        return first_even, 0
    even_count = ((stop0 - 1 - first_even) // 2) + 1
    return first_even, even_count


def count_divisible_in_even_progression(first_even: int, even_count: int, d: int) -> int:
    """
    Count elements of

      first_even, first_even + 2, ..., first_even + 2*(even_count-1)

    divisible by `d`.
    """
    if even_count <= 0:
        return 0
    g = math.gcd(2, d)
    if first_even % g != 0:
        return 0
    a = first_even // g
    b = 2 // g
    mod = d // g
    if mod == 1:
        return even_count
    # `b` is invertible mod `mod`.
    inv_b = pow(b, -1, mod)
    k0 = ((-a) * inv_b) % mod
    if k0 >= even_count:
        return 0
    return 1 + (even_count - 1 - k0) // mod


def divisors_cached(n: int, ctx: dict[str, object]) -> list[int]:
    cache = ctx["divisor_list_cache"]
    if n not in cache:
        spf = ctx["spf"]
        cache[n] = divisors_from_factorization(factorization(n, spf))
    return cache[n]


def gcd_class_count_in_even_progression(
    q: int,
    g: int,
    first_even: int,
    even_count: int,
    ctx: dict[str, object],
) -> int:
    cache = ctx["gcd_class_count_cache"]
    key = (q, g, first_even, even_count)
    if key in cache:
        return cache[key]
    mu = ctx["mu"]
    div_count_cache = ctx["divisibility_count_cache"]
    total = 0
    q_over_g = q // g
    for d in divisors_cached(q_over_g, ctx):
        div_key = (first_even, even_count, g * d)
        cnt = div_count_cache.get(div_key)
        if cnt is None:
            cnt = count_divisible_in_even_progression(first_even, even_count, g * d)
            div_count_cache[div_key] = cnt
        total += mu[d] * cnt
    cache[key] = total
    return total


def gcd_class_pair_count_in_even_progression(
    q: int,
    q2: int,
    g: int,
    h: int,
    first_even: int,
    even_count: int,
    ctx: dict[str, object],
) -> int:
    cache = ctx["gcd_class_pair_count_cache"]
    key = (q, q2, g, h, first_even, even_count)
    if key in cache:
        return cache[key]
    mu = ctx["mu"]
    div_count_cache = ctx["divisibility_count_cache"]
    total = 0
    q_over_g = q // g
    q2_over_h = q2 // h
    for d in divisors_cached(q_over_g, ctx):
        mu_d = mu[d]
        gd = g * d
        for e in divisors_cached(q2_over_h, ctx):
            mod = math.lcm(gd, h * e)
            div_key = (first_even, even_count, mod)
            cnt = div_count_cache.get(div_key)
            if cnt is None:
                cnt = count_divisible_in_even_progression(first_even, even_count, mod)
                div_count_cache[div_key] = cnt
            total += mu_d * mu[e] * cnt
    cache[key] = total
    return total


def count_coprime_shifted(start: int, modulus: int, length: int) -> int:
    return sum(1 for t in range(length) if math.gcd(modulus, start + t) == 1)


def decimal_to_q_literal(x: float, places: int = 12) -> str:
    """
    Convert a finite decimal approximation into an exact `ℚ` literal string.

    This is intentionally a payload/export helper: it mirrors the printed audit value with a fixed
    decimal denominator so the result can be copied directly into Lean `CheckLE` certificate data.
    It does not by itself certify that the audited decimal equals the true Lean object.
    """
    dec = Decimal(f"{x:.{places}f}")
    scaled = int(dec.scaleb(places))
    denom = 10 ** places
    return f"({scaled} : ℚ) / {denom}"


def fraction_to_q_literal(x: Fraction) -> str:
    return f"({x.numerator} : ℚ) / {x.denominator}"


def nat_list_to_lean_finset_literal(xs: list[int]) -> str:
    body = ", ".join(str(x) for x in xs)
    return f"([{body}] : List ℕ).toFinset"


def decimal_string_to_fraction(s: str) -> Fraction:
    dec = Decimal(s)
    num, den = dec.as_integer_ratio()
    return Fraction(num, den)


def float_to_fixed_fraction(x: float, places: int = 12) -> Fraction:
    dec = Decimal(f"{x:.{places}f}")
    num, den = dec.as_integer_ratio()
    return Fraction(num, den)


def surrogate_coeff_rat(q: int, mu: list[int], phi: list[int]) -> Fraction:
    if mu[q] == 0:
        return Fraction(0, 1)
    return Fraction(5, phi[q] ** 2)


def ramanujan_gcd_class_coeff_rat(q: int, g: int, mu: list[int], phi: list[int]) -> Fraction:
    return Fraction(mu[q // g] * phi[g], 1)


def centered_ramanujan_window_average_rat(
    X: int,
    q: int,
    mu: list[int],
    phi: list[int],
    even_window: list[int],
    even_window_card: int,
) -> Fraction:
    total = 0
    for N in even_window:
        total += ramanujan_sum(q, N, mu, phi)
    return Fraction(total, even_window_card)


def centered_ramanujan_window_energy_rat(
    X: int,
    q: int,
    mu: list[int],
    phi: list[int],
    even_window: list[int],
    even_window_card: int,
) -> Fraction:
    avg = centered_ramanujan_window_average_rat(X, q, mu, phi, even_window, even_window_card)
    total = Fraction(0, 1)
    for N in even_window:
        obs = Fraction(ramanujan_sum(q, N, mu, phi), 1) - avg
        total += obs * obs
    return total


def surrogate_diagonal_energy_q_rat(
    X: int,
    q: int,
    mu: list[int],
    phi: list[int],
    even_window: list[int],
    even_window_card: int,
) -> Fraction:
    return (
        surrogate_coeff_rat(q, mu, phi) ** 2
        * centered_ramanujan_window_energy_rat(X, q, mu, phi, even_window, even_window_card)
    )


def even_window_progression(X: int) -> tuple[int, int]:
    first_even = X if X % 2 == 0 else X + 1
    return first_even, ((H + 1) + 1) // 2


def build_surrogate_diagonal_exact_context(
    mu: list[int],
    phi: list[int],
    spf: list[int],
    support: list[int],
) -> dict[str, object]:
    coeff_rat: dict[int, Fraction] = {}
    divisors_by_q: dict[int, list[int]] = {}
    gcd_coeff_by_q: dict[int, dict[int, Fraction]] = {}

    for q in support:
        coeff_rat[q] = surrogate_coeff_rat(q, mu, phi)
        fac_q = factorization(q, spf)
        divs_q = divisors_from_factorization(fac_q)
        divisors_by_q[q] = divs_q
        gcd_coeff_by_q[q] = {
            g: ramanujan_gcd_class_coeff_rat(q, g, mu, phi)
            for g in divs_q
        }

    return {
        "mu": mu,
        "spf": spf,
        "coeff_rat": coeff_rat,
        "divisors_by_q": divisors_by_q,
        "gcd_coeff_by_q": gcd_coeff_by_q,
        "divisor_list_cache": {},
        "divisibility_count_cache": {},
        "gcd_class_count_cache": {},
    }


def centered_ramanujan_window_average_rat_cached(
    X: int,
    q: int,
    even_window_card: int,
    ctx: dict[str, object],
) -> Fraction:
    first_even, even_count = even_window_progression(X)
    divs_q = ctx["divisors_by_q"][q]
    coeff_q = ctx["gcd_coeff_by_q"][q]
    total = Fraction(0, 1)
    for g in divs_q:
        count_g = gcd_class_count_in_even_progression(q, g, first_even, even_count, ctx)
        total += coeff_q[g] * count_g
    return total / even_window_card


def centered_ramanujan_window_energy_rat_cached(
    X: int,
    q: int,
    even_window_card: int,
    ctx: dict[str, object],
) -> Fraction:
    first_even, even_count = even_window_progression(X)
    divs_q = ctx["divisors_by_q"][q]
    coeff_q = ctx["gcd_coeff_by_q"][q]
    avg = centered_ramanujan_window_average_rat_cached(X, q, even_window_card, ctx)
    total = Fraction(0, 1)
    for g in divs_q:
        count_g = gcd_class_count_in_even_progression(q, g, first_even, even_count, ctx)
        obs = coeff_q[g] - avg
        total += count_g * obs * obs
    return total


def surrogate_diagonal_energy_q_rat_cached(
    X: int,
    q: int,
    even_window_card: int,
    ctx: dict[str, object],
) -> Fraction:
    return (
        ctx["coeff_rat"][q] ** 2
        * centered_ramanujan_window_energy_rat_cached(X, q, even_window_card, ctx)
    )


def ramanujan_gcd_class_window_average_rat(
    X: int, q: int, g: int, even_window_card: int
) -> Fraction:
    count = 0
    start = X if X % 2 == 0 else X + 1
    for N in range(start, X + H + 1, 2):
        if math.gcd(q, N) == g:
            count += 1
    return Fraction(count, even_window_card)


def centered_ramanujan_pair_boundary_term_rat(
    X: int,
    q: int,
    q2: int,
    mu: list[int],
    phi: list[int],
    spf: list[int],
    even_window_card: int,
) -> Fraction:
    fac_q = factorization(q, spf)
    fac_q2 = factorization(q2, spf)
    divs_q = divisors_from_factorization(fac_q)
    divs_q2 = divisors_from_factorization(fac_q2)
    avg_q = {g: ramanujan_gcd_class_window_average_rat(X, q, g, even_window_card) for g in divs_q}
    avg_q2 = {h: ramanujan_gcd_class_window_average_rat(X, q2, h, even_window_card) for h in divs_q2}

    P = block_period(q, q2)
    m = (H + 1) // P
    r = (H + 1) % P

    out = Fraction(0, 1)
    for g in divs_q:
        c_g = ramanujan_gcd_class_coeff_rat(q, g, mu, phi)
        for h in divs_q2:
            c_h = ramanujan_gcd_class_coeff_rat(q2, h, mu, phi)
            rem = Fraction(0, 1)
            for k in range(r):
                N = X + m * P + k
                if N % 2 != 0:
                    continue
                ind_g = Fraction(1 if math.gcd(q, N) == g else 0, 1)
                ind_h = Fraction(1 if math.gcd(q2, N) == h else 0, 1)
                rem += (ind_g - avg_q[g]) * (ind_h - avg_q2[h])
            out += c_g * c_h * rem
    return out


def surrogate_boundary_pair_contribution_rat(
    X: int,
    q: int,
    q2: int,
    mu: list[int],
    phi: list[int],
    spf: list[int],
    even_window_card: int,
) -> Fraction:
    if q == q2:
        return Fraction(0, 1)
    return (
        surrogate_coeff_rat(q, mu, phi)
        * surrogate_coeff_rat(q2, mu, phi)
        * centered_ramanujan_pair_boundary_term_rat(X, q, q2, mu, phi, spf, even_window_card)
    )


def build_surrogate_boundary_exact_context(
    X: int,
    mu: list[int],
    phi: list[int],
    spf: list[int],
    even_window_card: int,
    support: list[int],
    progress: bool = False,
    progress_every_q: int = 500,
) -> dict[str, object]:
    coeff_rat: dict[int, Fraction] = {}
    divisors_by_q: dict[int, list[int]] = {}
    avg_by_q: dict[int, dict[int, Fraction]] = {}
    gcd_coeff_by_q: dict[int, dict[int, Fraction]] = {}

    started = time.time()
    for i, q in enumerate(support, start=1):
        coeff_rat[q] = surrogate_coeff_rat(q, mu, phi)
        fac_q = factorization(q, spf)
        divs_q = divisors_from_factorization(fac_q)
        divisors_by_q[q] = divs_q
        avg_by_q[q] = {
            g: ramanujan_gcd_class_window_average_rat(X, q, g, even_window_card)
            for g in divs_q
        }
        gcd_coeff_by_q[q] = {
            g: ramanujan_gcd_class_coeff_rat(q, g, mu, phi)
            for g in divs_q
        }
        if progress and (i % progress_every_q == 0 or i == len(support)):
            elapsed = time.time() - started
            print(
                f"[boundary-rat:precompute] q={i}/{len(support)} elapsed={elapsed:.1f}s",
                file=sys.stderr,
                flush=True,
            )

    return {
        "mu": mu,
        "spf": spf,
        "coeff_rat": coeff_rat,
        "divisors_by_q": divisors_by_q,
        "avg_by_q": avg_by_q,
        "gcd_coeff_by_q": gcd_coeff_by_q,
        "divisor_list_cache": {},
        "divisibility_count_cache": {},
        "gcd_class_count_cache": {},
        "gcd_class_pair_count_cache": {},
    }


def centered_ramanujan_pair_periodic_main_term_rat_cached(
    X: int,
    q: int,
    q2: int,
    ctx: dict[str, object],
) -> Fraction:
    P = block_period(q, q2)
    full_blocks = (H + 1) // P
    if full_blocks == 0:
        return Fraction(0, 1)

    divisors_by_q = ctx["divisors_by_q"]
    avg_by_q = ctx["avg_by_q"]
    gcd_coeff_by_q = ctx["gcd_coeff_by_q"]
    coeff_rat = ctx["coeff_rat"]

    divs_q = divisors_by_q[q]
    divs_q2 = divisors_by_q[q2]
    avg_q = avg_by_q[q]
    avg_q2 = avg_by_q[q2]
    coeff_q = gcd_coeff_by_q[q]
    coeff_q2 = gcd_coeff_by_q[q2]

    first_even, even_count = full_block_even_progression(X, P)
    out = Fraction(0, 1)
    coeff_pair = coeff_rat[q] * coeff_rat[q2]
    full_blocks_rat = Fraction(full_blocks, 1)
    even_count_rat = Fraction(even_count, 1)
    for g in divs_q:
        avg_g = avg_q[g]
        left = Fraction(gcd_class_count_in_even_progression(q, g, first_even, even_count, ctx), 1)
        c_g = coeff_q[g]
        for h in divs_q2:
            avg_h = avg_q2[h]
            right = Fraction(gcd_class_count_in_even_progression(q2, h, first_even, even_count, ctx), 1)
            pair = Fraction(
                gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, ctx),
                1,
            )
            c_h = coeff_q2[h]
            centered_full_block = pair - avg_h * left - avg_g * right + avg_g * avg_h * even_count_rat
            out += coeff_pair * c_g * c_h * full_blocks_rat * centered_full_block
    return out


def lean_nat_list(values: list[int]) -> str:
    return "[" + ", ".join(str(v) for v in values) + "]"


def emit_periodic_main_pair_primitive_lean_header(imports: list[str] | None = None) -> None:
    if imports is None:
        imports = ["Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain"]
    for module in imports:
        print(f"import {module}")
    print()
    print("set_option maxHeartbeats 0")
    print("set_option maxRecDepth 100000")
    print("set_option linter.constructorNameAsVariable false")
    print()
    print("namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")
    print()
    print("open Goldbach")
    print("open Goldbach.BankParams")
    print("open Goldbach.Windows")
    print()


def emit_periodic_main_pair_primitive_lean_footer() -> None:
    print("end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")


def emit_periodic_main_record_batch_wrapper(
    *,
    X: int,
    label: str,
    records: list[dict[str, object]],
) -> None:
    pairs_name = f"PeriodicMainRecords{label}Pairs"
    value_name = f"PeriodicMainRecords{label}Value"
    total_name = f"PeriodicMainRecords{label}Total"
    support_subset_name = f"PeriodicMainRecords{label}_support_subset"
    value_on_records_name = f"PeriodicMainRecords{label}_value_on_records"
    records_sum_name = f"PeriodicMainRecords{label}_records_sum"

    def pair_term(q: int, q2: int) -> str:
        return f"({q}, {q2})"

    def support_theorem_name(q: int, q2: int) -> str:
        return f"PeriodicMainRecords{label}_support_{q}_{q2}"

    total = Fraction(0, 1)
    print(f"def {pairs_name} : Finset (ℕ × ℕ) :=")
    print("  [" + ", ".join(pair_term(int(r["q"]), int(r["q2"])) for r in records) + "].toFinset")
    print()
    print(f"noncomputable def {value_name} (p : ℕ × ℕ) : ℚ :=")
    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        value = Fraction(int(record["value_num"]), int(record["value_den"]))
        total += value
        print(f"  if p = {pair_term(q, q2)} then {fraction_to_q_literal(value)} else")
    print("  0")
    print()
    print(f"def {total_name} : ℚ := {fraction_to_q_literal(total)}")
    print()
    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        print(f"theorem {support_theorem_name(q, q2)} :")
        print(f"    {pair_term(q, q2)} ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by")
        print(f"  have hqCoeff : {q} ∈ PeriodicMainCoeffSupportExplicit := by")
        print("    unfold PeriodicMainCoeffSupportExplicit")
        print("    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩")
        print(f"  have hq2Coeff : {q2} ∈ PeriodicMainCoeffSupportExplicit := by")
        print("    unfold PeriodicMainCoeffSupportExplicit")
        print("    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩")
        print(f"  have hqActive : {q} ∈ PeriodicMainActiveSupportExplicit := by")
        print("    unfold PeriodicMainActiveSupportExplicit")
        print("    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩")
        print(f"  have hq2Active : {q2} ∈ PeriodicMainActiveSupportExplicit := by")
        print("    unfold PeriodicMainActiveSupportExplicit")
        print("    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩")
        print("  unfold PeriodicMainFullBlockOrderedPairSupportExplicit")
        print("  exact Finset.mem_filter.mpr ⟨by")
        print("    unfold PeriodicMainActiveOrderedPairSupportExplicit")
        print("    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,")
        print("    by")
        print("      constructor")
        print("      · norm_num")
        print("      · norm_num [centeredRamanujanPairBlockPeriod, H]")
        print("  ⟩")
        print()
    print(f"theorem {support_subset_name} :")
    print(f"    {pairs_name} ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by")
    print("  intro p hp")
    print(f"  simp [{pairs_name}] at hp")
    rcases_pattern = " | ".join("h" for _ in records)
    print(f"  rcases hp with {rcases_pattern}")
    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        print("  · subst p")
        print(f"    exact {support_theorem_name(q, q2)}")
    print()
    print(f"theorem {value_on_records_name} :")
    print(f"    ∀ p ∈ {pairs_name},")
    print(f"      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = {value_name} p := by")
    print("  intro p hp")
    print(f"  simp [{pairs_name}] at hp")
    print(f"  rcases hp with {rcases_pattern}")
    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        print("  · subst p")
        print(
            f"    simp [{value_name}, periodicMainPair_{q}_{q2}_X{X}_orderedSummand]"
        )
    print()
    print(f"theorem {records_sum_name} :")
    print(f"    (∑ p ∈ {pairs_name}, {value_name} p) = {total_name} := by")
    print(f"  norm_num [{pairs_name}, {value_name}, {total_name}]")
    print()


def emit_periodic_main_zero_record_batch_wrapper(
    *,
    X: int,
    label: str,
    records: list[dict[str, object]],
) -> None:
    pairs_name = f"PeriodicMainRecords{label}Pairs"
    value_name = f"PeriodicMainRecords{label}Value"
    total_name = f"PeriodicMainRecords{label}Total"
    value_on_records_name = f"PeriodicMainRecords{label}_value_on_records"
    records_sum_name = f"PeriodicMainRecords{label}_records_sum"

    def pair_term(q: int, q2: int) -> str:
        return f"({q}, {q2})"

    for record in records:
        value = Fraction(int(record["value_num"]), int(record["value_den"]))
        if value != 0:
            q = int(record["q"])
            q2 = int(record["q2"])
            raise SystemExit(f"zero record batch contains nonzero value at ({q},{q2}): {value}")

    print(f"def {pairs_name} : Finset (ℕ × ℕ) :=")
    print("  [" + ", ".join(pair_term(int(r["q"]), int(r["q2"])) for r in records) + "].toFinset")
    print()
    print(f"noncomputable def {value_name} (_p : ℕ × ℕ) : ℚ :=")
    print("  0")
    print()
    print(f"def {total_name} : ℚ := 0")
    print()
    print(f"theorem {value_on_records_name} :")
    print(f"    ∀ p ∈ {pairs_name},")
    print("      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by")
    print("  intro p hp")
    print(f"  simp [{pairs_name}] at hp")
    rcases_pattern = " | ".join("h" for _ in records)
    print(f"  rcases hp with {rcases_pattern}")
    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        print("  · subst p")
        print(f"    simpa using periodicMainPair_{q}_{q2}_X{X}_orderedSummand")
    print()
    print(f"theorem {records_sum_name} :")
    print(f"    (∑ p ∈ {pairs_name}, {value_name} p) = {total_name} := by")
    print(f"  norm_num [{pairs_name}, {value_name}, {total_name}]")
    print()


def left_assoc_or_pattern(names: list[str]) -> str:
    if not names:
        raise ValueError("left_assoc_or_pattern requires at least one name")
    pattern = names[0]
    for name in names[1:]:
        pattern = f"({pattern} | {name})"
    return pattern


def emit_periodic_main_pair_record_lean_chunk_files(
    *,
    X: int,
    records: list[dict[str, object]],
    zero_record_batch: bool,
    out_dir: str,
    file_prefix: str,
    label_prefix: str,
    chunk_size: int,
    index_offset: int = 0,
    skip_existing: bool = False,
    force_top_level_helpers: bool = False,
) -> int:
    if chunk_size <= 0:
        raise SystemExit("--periodic-main-record-file-chunk-size must be positive")
    if not records:
        raise SystemExit("selected periodic-main record slice is empty")

    os.makedirs(out_dir, exist_ok=True)
    q_support = sorted(
        {int(record["q"]) for record in records}
        | {int(record["q2"]) for record in records}
    )
    mu, phi = mobius_phi_sieve(Q0)
    spf = spf_sieve(Q0)
    even_card = len(even_window_points(X))
    exact_ctx = build_surrogate_boundary_exact_context(X, mu, phi, spf, even_card, q_support)

    chunk_count = (len(records) + chunk_size - 1) // chunk_size
    for chunk_idx in range(chunk_count):
        start = chunk_idx * chunk_size
        end = min(len(records), start + chunk_size)
        global_start = index_offset + start
        global_end = index_offset + end
        global_chunk_idx = index_offset // chunk_size + chunk_idx
        chunk_records = records[start:end]
        label = f"{label_prefix}{global_chunk_idx:03d}"
        path = os.path.join(out_dir, f"{file_prefix}{global_chunk_idx:03d}.lean")
        if skip_existing and os.path.exists(path):
            print(f"[skip] {path}", file=sys.stderr)
            continue
        with open(path, "w", encoding="utf-8") as fh, contextlib.redirect_stdout(fh):
            emit_periodic_main_pair_primitive_lean_header()
            record_kind = "zero-record" if zero_record_batch else "nonzero-record"
            print(
                f"/- Generated periodic-main {record_kind} proofs for selected JSON indices "
                f"[{global_start},{global_end}). -/"
            )
            print()
            for record in chunk_records:
                q = int(record["q"])
                q2 = int(record["q2"])
                expected = Fraction(int(record["value_num"]), int(record["value_den"]))
                emit_periodic_main_pair_primitive_lean_theorems(
                    X=X,
                    q=q,
                    q2=q2,
                    exact_ctx=exact_ctx,
                    expected_summand=expected,
                    force_top_level_helpers=force_top_level_helpers,
                )
            if zero_record_batch:
                emit_periodic_main_zero_record_batch_wrapper(
                    X=X,
                    label=label,
                    records=chunk_records,
                )
            else:
                emit_periodic_main_record_batch_wrapper(
                    X=X,
                    label=label,
                    records=chunk_records,
                )
            emit_periodic_main_pair_primitive_lean_footer()
        print(f"[write] {path} records=[{global_start},{global_end})", file=sys.stderr)
    return chunk_count


def lean_module_name_for_path(path: str) -> str:
    no_ext = os.path.splitext(path)[0]
    parts = no_ext.split(os.sep)
    if "Goldbach" in parts:
        parts = parts[parts.index("Goldbach"):]
    return ".".join(parts)


def emit_periodic_main_pair_record_split_lean_files(
    *,
    X: int,
    records: list[dict[str, object]],
    out_dir: str,
    file_prefix: str,
    label_prefix: str,
    index_offset: int = 0,
    skip_existing: bool = False,
    row_part_size: int = 8,
    inline_row_parts: bool = False,
    disable_q42_cancel: bool = False,
) -> int:
    if not records:
        raise SystemExit("selected periodic-main record slice is empty")
    if row_part_size <= 0:
        raise SystemExit("--periodic-main-split-row-part-size must be positive")

    os.makedirs(out_dir, exist_ok=True)
    q_support = sorted(
        {int(record["q"]) for record in records}
        | {int(record["q2"]) for record in records}
    )
    mu, phi = mobius_phi_sieve(Q0)
    spf = spf_sieve(Q0)
    even_card = len(even_window_points(X))
    exact_ctx = build_surrogate_boundary_exact_context(X, mu, phi, spf, even_card, q_support)

    def emit_header(fh, imports: list[str]) -> None:
        with contextlib.redirect_stdout(fh):
            emit_periodic_main_pair_primitive_lean_header(imports=imports)

    def emit_footer(fh) -> None:
        with contextlib.redirect_stdout(fh):
            emit_periodic_main_pair_primitive_lean_footer()

    def term_expr_lines(q: int, q2: int, g: int | str, h: int | str, *, indent: str = "      ") -> list[str]:
        return [
            f"{indent}ramanujanGcdClassCoeffRat {q} {g} * ramanujanGcdClassCoeffRat {q2} {h}",
            f"{indent}  * ((((H + 1) / centeredRamanujanPairBlockPeriod {q} {q2}) : ℕ)",
            f"{indent}      • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} {g} {h}",
            f"{indent}          - ramanujanGcdClassWindowAverageRat X0 {q2} {h}",
            f"{indent}              * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q} {g}",
            f"{indent}          - ramanujanGcdClassWindowAverageRat X0 {q} {g}",
            f"{indent}              * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q2} {h}",
            f"{indent}          + ramanujanGcdClassWindowAverageRat X0 {q} {g}",
            f"{indent}              * ramanujanGcdClassWindowAverageRat X0 {q2} {h}",
            f"{indent}              * evenRamanujanBlockCountRat {q} {q2}))",
        ]

    def emit_block_periodic_count_proof(
        *,
        theorem_name: str,
        q: int,
        q2: int,
        q0: int,
        g0: int,
        expected: int,
        indent: str = "  ",
    ) -> list[str]:
        lines = [
            f"{indent}have {theorem_name} : "
            f"rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q0} {g0} = ({expected} : ℚ) := by"
        ]
        quotient = q0 // g0 if g0 != 0 else 0
        if g0 % 2 == 0:
            lines.extend([
                f"{indent}  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]",
                f"{indent}  all_goals native_decide",
            ])
        elif quotient % 2 == 0 and expected == 0:
            lines.extend([
                f"{indent}  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]",
                f"{indent}  all_goals native_decide",
            ])
        else:
            lines.extend([
                f"{indent}  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]",
                f"{indent}  all_goals native_decide",
            ])
        return lines

    def emit_pair_resolved_count_proof(
        *,
        theorem_name: str,
        q: int,
        q2: int,
        g: int,
        h: int,
        expected: int,
        indent: str = "  ",
    ) -> list[str]:
        lines = [
            f"{indent}have {theorem_name} : "
            f"rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} {g} {h} = ({expected} : ℚ) := by"
        ]
        lcm_gh = math.lcm(g, h)
        compatible = math.gcd(q // g, lcm_gh // g) == 1 and math.gcd(q2 // h, lcm_gh // h) == 1
        if expected == 0 and not compatible:
            lines.extend([
                f"{indent}  have hcompat : ¬ ramanujanGcdClassJointCompatibility {q} {q2} {g} {h} := by",
                f"{indent}    native_decide",
                f"{indent}  unfold rawEvenRamanujanGcdClassPairBlockResolvedCountRat",
                f"{indent}  simp [hcompat]",
            ])
        else:
            joint_modulus = (
                math.lcm(q // g, q2 // h) if g != 0 and h != 0 else 0
            )
            lcm_gh_even = lcm_gh % 2 == 0
            joint_modulus_even = joint_modulus % 2 == 0
            lines.extend([
                f"{indent}  rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]",
            ])
            if lcm_gh_even:
                lines.extend([
                    f"{indent}  · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]",
                    f"{indent}    all_goals native_decide",
                ])
            elif joint_modulus_even and expected == 0:
                lines.extend([
                    f"{indent}  · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]",
                    f"{indent}    all_goals native_decide",
                ])
            else:
                lines.extend([
                    f"{indent}  · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]",
                    f"{indent}    all_goals native_decide",
                ])
            lines.append(f"{indent}  · norm_num [ramanujanGcdClassJointCompatibility]")
        return lines

    def can_use_right_odd_structural_zero(q2: int, g: int, h: int) -> bool:
        # Existing Lean zero lemmas cover the right-even/right-odd case when
        # the reduced pair lcm is odd. That is exactly the odd-left/odd-right
        # divisor case; other parity cases keep the conservative atom proof.
        return q2 % 2 == 0 and g % 2 == 1 and h % 2 == 1

    def can_use_left_odd_structural_zero(q: int, g: int) -> bool:
        return q % 2 == 0 and g % 2 == 1

    def emit_right_odd_structural_zero_proofs(
        *,
        q: int,
        q2: int,
        g: int,
        h: int,
        indent: str = "  ",
    ) -> list[str]:
        lines = [
            f"{indent}have hAvgRight : ramanujanGcdClassWindowAverageRat X0 {q2} {h} = (0 : ℚ) / 1 := by",
            f"{indent}  native_decide",
            f"{indent}have hBlockRight : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q2} {h} = (0 : ℚ) := by",
            f"{indent}  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]",
            f"{indent}  all_goals native_decide",
        ]
        lines.extend(
            emit_pair_resolved_count_proof(
                theorem_name="hPair",
                q=q,
                q2=q2,
                g=g,
                h=h,
                expected=0,
                indent=indent,
            )
        )
        return lines

    def emit_left_odd_structural_zero_proofs(
        *,
        q: int,
        q2: int,
        g: int,
        h: int,
        expected_pair: int,
        indent: str = "  ",
    ) -> list[str]:
        lines = [
            f"{indent}have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 {q} {g} = (0 : ℚ) / 1 := by",
            f"{indent}  native_decide",
            f"{indent}have hBlockLeft : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q} {g} = (0 : ℚ) := by",
            f"{indent}  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]",
            f"{indent}  all_goals native_decide",
        ]
        lines.extend(
            emit_pair_resolved_count_proof(
                theorem_name="hPair",
                q=q,
                q2=q2,
                g=g,
                h=h,
                expected=expected_pair,
                indent=indent,
            )
        )
        return lines

    def split_union_expr(chunk_names: list[str], end: int | None = None) -> str:
        names = chunk_names if end is None else chunk_names[:end]
        expr = names[0]
        for name in names[1:]:
            expr = f"({expr} ∪ {name})"
        return expr

    def emit_split_record(record: dict[str, object], record_index: int) -> None:
        q = int(record["q"])
        q2 = int(record["q2"])
        expected = Fraction(int(record["value_num"]), int(record["value_den"]))
        name = f"periodicMainPair_{q}_{q2}_X{X}"
        label = f"{label_prefix}{record_index:03d}"
        stem = f"{file_prefix}{record_index:03d}"
        wrapper_path = os.path.join(out_dir, f"{stem}.lean")
        if skip_existing and os.path.exists(wrapper_path):
            print(f"[skip] {wrapper_path}", file=sys.stderr)
            return

        divs_q = exact_ctx["divisors_by_q"][q]
        divs_q2 = exact_ctx["divisors_by_q"][q2]
        first_even, even_count = full_block_even_progression(X, block_period(q, q2))
        full_blocks = (H + 1) // block_period(q, q2)
        even_count_rat = Fraction(even_count, 1)
        coeff_q = exact_ctx["coeff_rat"][q]
        coeff_q2 = exact_ctx["coeff_rat"][q2]
        summand_value = centered_ramanujan_pair_periodic_main_term_rat_cached(X, q, q2, exact_ctx)
        if summand_value != expected:
            raise SystemExit(
                f"record ({q},{q2}) value mismatch: generated {summand_value} but JSON record has {expected}"
            )
        centered_term = Fraction(0, 1) if coeff_q == 0 or coeff_q2 == 0 else summand_value / (coeff_q * coeff_q2)

        row_values: dict[int, Fraction] = {g: Fraction(0, 1) for g in divs_q}
        term_values: dict[tuple[int, int], Fraction] = {}
        block_left_values = {
            g: gcd_class_count_in_even_progression(q, g, first_even, even_count, exact_ctx)
            for g in divs_q
        }
        block_right_values = {
            h: gcd_class_count_in_even_progression(q2, h, first_even, even_count, exact_ctx)
            for h in divs_q2
        }
        pair_values = {
            (g, h): gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, exact_ctx)
            for g in divs_q
            for h in divs_q2
        }
        for g in divs_q:
            avg_g = exact_ctx["avg_by_q"][q][g]
            left = Fraction(block_left_values[g], 1)
            c_g = exact_ctx["gcd_coeff_by_q"][q][g]
            for h in divs_q2:
                avg_h = exact_ctx["avg_by_q"][q2][h]
                right = Fraction(block_right_values[h], 1)
                pair = Fraction(pair_values[(g, h)], 1)
                c_h = exact_ctx["gcd_coeff_by_q"][q2][h]
                centered_full_block = pair - avg_h * left - avg_g * right + avg_g * avg_h * even_count_rat
                term_value = c_g * c_h * Fraction(full_blocks, 1) * centered_full_block
                term_values[(g, h)] = term_value
                row_values[g] += term_value

        base_import = "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain"

        def emit_q42_cancel_split_record() -> bool:
            if q != 42 or expected != 0:
                return False
            if divs_q != [1, 2, 3, 6, 7, 14, 21, 42]:
                return False
            zero_rows = [1, 3, 7, 21]
            cancel_pairs = [(2, 6), (14, 42)]
            if any(row_values[g] != 0 for g in zero_rows):
                return False
            if any(row_values[g] + row_values[gp] != 0 for g, gp in cancel_pairs):
                return False
            if any(term_values[(g, h)] + term_values[(gp, h)] != 0
                   for g, gp in cancel_pairs for h in divs_q2):
                return False

            fact_prefix = f"{name}_q42Facts"
            fact_stem = f"{stem}Q42Facts"
            fact_path = os.path.join(out_dir, f"{fact_stem}.lean")
            fact_module = lean_module_name_for_path(fact_path)
            paired_rows = sorted({g0 for pair in cancel_pairs for g0 in pair})
            with open(fact_path, "w", encoding="utf-8") as fh:
                emit_header(fh, [base_import])
                for g0 in paired_rows:
                    print(f"theorem {fact_prefix}_coeffLeft_{g0} : ramanujanGcdClassCoeffRat {q} {g0} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q][g0])} := by", file=fh)
                    print("  native_decide", file=fh)
                    print(file=fh)
                for h in divs_q2:
                    print(f"theorem {fact_prefix}_coeffRight_{h} : ramanujanGcdClassCoeffRat {q2} {h} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q2][h])} := by", file=fh)
                    print("  native_decide", file=fh)
                    print(file=fh)
                for g0 in paired_rows:
                    print(f"theorem {fact_prefix}_avgLeft_{g0} : ramanujanGcdClassWindowAverageRat X0 {q} {g0} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q][g0])} := by", file=fh)
                    print("  native_decide", file=fh)
                    print(file=fh)
                for h in divs_q2:
                    print(f"theorem {fact_prefix}_avgRight_{h} : ramanujanGcdClassWindowAverageRat X0 {q2} {h} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q2][h])} := by", file=fh)
                    print("  native_decide", file=fh)
                    print(file=fh)
                for g0 in paired_rows:
                    lines = emit_block_periodic_count_proof(
                        theorem_name=f"{fact_prefix}_blockLeft_{g0}",
                        q=q,
                        q2=q2,
                        q0=q,
                        g0=g0,
                        expected=block_left_values[g0],
                        indent="",
                    )
                    lines[0] = lines[0].replace("have ", "theorem ", 1)
                    for line in lines:
                        print(line, file=fh)
                    print(file=fh)
                for h in divs_q2:
                    lines = emit_block_periodic_count_proof(
                        theorem_name=f"{fact_prefix}_blockRight_{h}",
                        q=q,
                        q2=q2,
                        q0=q2,
                        g0=h,
                        expected=block_right_values[h],
                        indent="",
                    )
                    lines[0] = lines[0].replace("have ", "theorem ", 1)
                    for line in lines:
                        print(line, file=fh)
                    print(file=fh)
                for g0 in paired_rows:
                    for h in divs_q2:
                        lines = emit_pair_resolved_count_proof(
                            theorem_name=f"{fact_prefix}_pair_{g0}_{h}",
                            q=q,
                            q2=q2,
                            g=g0,
                            h=h,
                            expected=pair_values[(g0, h)],
                            indent="",
                        )
                        lines[0] = lines[0].replace("have ", "theorem ", 1)
                        for line in lines:
                            print(line, file=fh)
                        print(file=fh)
                emit_footer(fh)

            row_modules: dict[int, str] = {}
            for g in zero_rows:
                row_stem = f"{stem}Row_{g}"
                row_path = os.path.join(out_dir, f"{row_stem}.lean")
                row_modules[g] = lean_module_name_for_path(row_path)
                with open(row_path, "w", encoding="utf-8") as fh:
                    emit_header(fh, [base_import])
                    print(f"theorem {name}_divRight_for_row_{g} : Nat.divisors {q2} = ({lean_nat_list(divs_q2)} : List ℕ).toFinset := by", file=fh)
                    print("  decide", file=fh)
                    print(file=fh)
                    print(f"def {name}_rowZeroChunk_{g} : Finset ℕ :=", file=fh)
                    print(f"  ({lean_nat_list(divs_q2)} : List ℕ).toFinset", file=fh)
                    print(file=fh)
                    print(f"def {name}_rowZeroValue_{g} : ℕ → ℚ", file=fh)
                    for h in divs_q2:
                        print(f"| {h} => (0 : ℚ)", file=fh)
                    print("| _ => 0", file=fh)
                    print(file=fh)
                    print(f"theorem {name}_row_{g} :", file=fh)
                    print(f"    (∑ h ∈ Nat.divisors {q2},", file=fh)
                    for line in term_expr_lines(q, q2, g, "h", indent="      "):
                        print(line, file=fh)
                    print(f"    ) = (0 : ℚ) := by", file=fh)
                    print(f"  rw [{name}_divRight_for_row_{g}]", file=fh)
                    print(f"  have hset : ({lean_nat_list(divs_q2)} : List ℕ).toFinset = {name}_rowZeroChunk_{g} := by", file=fh)
                    print("    native_decide", file=fh)
                    print("  rw [hset]", file=fh)
                    print("  have hsum :", file=fh)
                    print(f"      (∑ h ∈ {name}_rowZeroChunk_{g},", file=fh)
                    for line in term_expr_lines(q, q2, g, "h", indent="        "):
                        print(line, file=fh)
                    print(f"      ) = (∑ h ∈ {name}_rowZeroChunk_{g}, {name}_rowZeroValue_{g} h) := by", file=fh)
                    print("    apply Finset.sum_congr rfl", file=fh)
                    print("    intro h hh", file=fh)
                    print(f"    simp [{name}_rowZeroChunk_{g}] at hh", file=fh)
                    print("    rcases hh with " + " | ".join(["rfl"] * len(divs_q2)), file=fh)
                    for h in divs_q2:
                        print("    · have hTerm :", file=fh)
                        for line in term_expr_lines(q, q2, g, h, indent="          "):
                            print(line, file=fh)
                        print("          = (0 : ℚ) := by", file=fh)
                        for line in emit_left_odd_structural_zero_proofs(
                            q=q,
                            q2=q2,
                            g=g,
                            h=h,
                            expected_pair=pair_values[(g, h)],
                            indent="        ",
                        ):
                            print(line, file=fh)
                        print("        rw [hPair, hAvgLeft, hBlockLeft]", file=fh)
                        print("        simp", file=fh)
                        print(f"      simpa [{name}_rowZeroValue_{g}] using hTerm", file=fh)
                    print("  rw [hsum]", file=fh)
                    print(f"  norm_num [{name}_rowZeroChunk_{g}, {name}_rowZeroValue_{g}]", file=fh)
                    print(file=fh)
                    emit_footer(fh)

            row_pair_modules: dict[tuple[int, int], str] = {}
            for g, gp in cancel_pairs:
                pair_term_modules: list[str] = []
                for h in divs_q2:
                    pair_term_stem = f"{stem}TermPair_{g}_{gp}_{h}"
                    pair_term_path = os.path.join(out_dir, f"{pair_term_stem}.lean")
                    pair_term_modules.append(lean_module_name_for_path(pair_term_path))
                    with open(pair_term_path, "w", encoding="utf-8") as fh:
                        emit_header(fh, [fact_module])
                        print(f"theorem {name}_termPair_{g}_{gp}_{h} :", file=fh)
                        for idx, line in enumerate(term_expr_lines(q, q2, g, h, indent="    ")):
                            prefix = "    (" if idx == 0 else ""
                            suffix = "" if idx + 1 < len(term_expr_lines(q, q2, g, h, indent="    ")) else ")"
                            print(prefix + line.lstrip() + suffix, file=fh)
                        print("    +", file=fh)
                        for idx, line in enumerate(term_expr_lines(q, q2, gp, h, indent="    ")):
                            prefix = "    (" if idx == 0 else ""
                            suffix = "" if idx + 1 < len(term_expr_lines(q, q2, gp, h, indent="    ")) else ")"
                            print(prefix + line.lstrip() + suffix, file=fh)
                        print("      = (0 : ℚ) := by", file=fh)
                        print("  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,", file=fh)
                        print(f"    {fact_prefix}_coeffLeft_{g}, {fact_prefix}_coeffLeft_{gp}, {fact_prefix}_coeffRight_{h},", file=fh)
                        print(f"    {fact_prefix}_avgLeft_{g}, {fact_prefix}_avgLeft_{gp}, {fact_prefix}_avgRight_{h},", file=fh)
                        print(f"    {fact_prefix}_blockLeft_{g}, {fact_prefix}_blockLeft_{gp}, {fact_prefix}_blockRight_{h},", file=fh)
                        print(f"    {fact_prefix}_pair_{g}_{h}, {fact_prefix}_pair_{gp}_{h}]", file=fh)
                        print(file=fh)
                        emit_footer(fh)

                row_pair_stem = f"{stem}Rows_{g}_{gp}"
                row_pair_path = os.path.join(out_dir, f"{row_pair_stem}.lean")
                row_pair_modules[(g, gp)] = lean_module_name_for_path(row_pair_path)
                with open(row_pair_path, "w", encoding="utf-8") as fh:
                    emit_header(fh, pair_term_modules)
                    print(f"theorem {name}_divRight_for_rows_{g}_{gp} : Nat.divisors {q2} = ({lean_nat_list(divs_q2)} : List ℕ).toFinset := by", file=fh)
                    print("  decide", file=fh)
                    print(file=fh)
                    print(f"def {name}_rowPairChunk_{g}_{gp} : Finset ℕ :=", file=fh)
                    print(f"  ({lean_nat_list(divs_q2)} : List ℕ).toFinset", file=fh)
                    print(file=fh)
                    print(f"def {name}_rowPairValue_{g}_{gp} : ℕ → ℚ", file=fh)
                    for h in divs_q2:
                        print(f"| {h} => (0 : ℚ)", file=fh)
                    print("| _ => 0", file=fh)
                    print(file=fh)
                    print(f"theorem {name}_rows_{g}_{gp} :", file=fh)
                    print(f"    (∑ h ∈ Nat.divisors {q2},", file=fh)
                    for line in term_expr_lines(q, q2, g, "h", indent="      "):
                        print(line, file=fh)
                    print("    ) +", file=fh)
                    print(f"    (∑ h ∈ Nat.divisors {q2},", file=fh)
                    for line in term_expr_lines(q, q2, gp, "h", indent="      "):
                        print(line, file=fh)
                    print(f"    ) = (0 : ℚ) := by", file=fh)
                    print(f"  rw [{name}_divRight_for_rows_{g}_{gp}]", file=fh)
                    print(f"  have hset : ({lean_nat_list(divs_q2)} : List ℕ).toFinset = {name}_rowPairChunk_{g}_{gp} := by", file=fh)
                    print("    native_decide", file=fh)
                    print("  rw [hset]", file=fh)
                    print("  rw [← Finset.sum_add_distrib]", file=fh)
                    print("  have hsum :", file=fh)
                    print(f"      (∑ h ∈ {name}_rowPairChunk_{g}_{gp},", file=fh)
                    print("        (", file=fh)
                    for line in term_expr_lines(q, q2, g, "h", indent="          "):
                        print(line, file=fh)
                    print("        ) +", file=fh)
                    print("        (", file=fh)
                    for line in term_expr_lines(q, q2, gp, "h", indent="          "):
                        print(line, file=fh)
                    print(f"        )) = (∑ h ∈ {name}_rowPairChunk_{g}_{gp}, {name}_rowPairValue_{g}_{gp} h) := by", file=fh)
                    print("    apply Finset.sum_congr rfl", file=fh)
                    print("    intro h hh", file=fh)
                    print(f"    simp [{name}_rowPairChunk_{g}_{gp}] at hh", file=fh)
                    print("    rcases hh with " + " | ".join(["rfl"] * len(divs_q2)), file=fh)
                    for h in divs_q2:
                        print(f"    · simpa [{name}_rowPairValue_{g}_{gp}] using {name}_termPair_{g}_{gp}_{h}", file=fh)
                    print("  rw [hsum]", file=fh)
                    print(f"  norm_num [{name}_rowPairChunk_{g}_{gp}, {name}_rowPairValue_{g}_{gp}]", file=fh)
                    print(file=fh)
                    emit_footer(fh)

            with open(wrapper_path, "w", encoding="utf-8") as fh:
                imports = [row_modules[g] for g in zero_rows] + [
                    row_pair_modules[pair] for pair in cancel_pairs
                ]
                emit_header(fh, imports)
                print(f"/- Split generated q=42 cancellation proof for selected JSON index {record_index}. -/", file=fh)
                print(file=fh)
                print(f"theorem {name}_divLeft : Nat.divisors {q} = ({lean_nat_list(divs_q)} : List ℕ).toFinset := by", file=fh)
                print("  decide", file=fh)
                print(file=fh)
                print(f"theorem {name}_centeredTerm :", file=fh)
                print(f"    centeredRamanujanPairPeriodicMainTermRat X0 {q} {q2} = (0 : ℚ) := by", file=fh)
                print("  unfold centeredRamanujanPairPeriodicMainTermRat", file=fh)
                print("  let R : ℕ → ℚ := fun g =>", file=fh)
                print(f"    ∑ h ∈ Nat.divisors {q2},", file=fh)
                for line in term_expr_lines(q, q2, "g", "h", indent="      "):
                    print(line, file=fh)
                print("  change (∑ g ∈ Nat.divisors 42, R g) = (0 : ℚ)", file=fh)
                print(f"  rw [{name}_divLeft]", file=fh)
                print("  have hreorder :", file=fh)
                print(f"      (∑ g ∈ ({lean_nat_list(divs_q)} : List ℕ).toFinset, R g)", file=fh)
                print("        = R 1 + R 3 + R 7 + R 21 + (R 2 + R 6) + (R 14 + R 42) := by", file=fh)
                print("    norm_num [Finset.sum_insert]", file=fh)
                print("    abel", file=fh)
                print("  rw [hreorder]", file=fh)
                for g in zero_rows:
                    print(f"  have hrow{g} : R {g} = (0 : ℚ) := by", file=fh)
                    print(f"    simpa [R] using {name}_row_{g}", file=fh)
                for g, gp in cancel_pairs:
                    print(f"  have hrows{g}_{gp} : R {g} + R {gp} = (0 : ℚ) := by", file=fh)
                    print(f"    simpa [R] using {name}_rows_{g}_{gp}", file=fh)
                print("  rw [hrow1, hrow3, hrow7, hrow21, hrows2_6, hrows14_42]", file=fh)
                print("  norm_num", file=fh)
                print(file=fh)
                print(f"theorem {name}_orderedSummand :", file=fh)
                print(f"    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk {q} {q2}) = (0 : ℚ) := by", file=fh)
                print(f"  have hneq : {q} ≠ {q2} := by", file=fh)
                print("    norm_num", file=fh)
                print(f"  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat {q} = {fraction_to_q_literal(coeff_q)} := by", file=fh)
                print("    native_decide", file=fh)
                print(f"  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat {q2} = {fraction_to_q_literal(coeff_q2)} := by", file=fh)
                print("    native_decide", file=fh)
                print(f"  have hvalue : ({fraction_to_q_literal(coeff_q)}) * ({fraction_to_q_literal(coeff_q2)}) * (0 : ℚ) = (0 : ℚ) := by", file=fh)
                print("    norm_num", file=fh)
                print("  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue", file=fh)
                print("    hneq hCoeffLeft hCoeffRight", file=fh)
                print(f"    {name}_centeredTerm", file=fh)
                print("    hvalue", file=fh)
                print(file=fh)
                with contextlib.redirect_stdout(fh):
                    emit_periodic_main_zero_record_batch_wrapper(X=X, label=label, records=[record])
                emit_footer(fh)
            print(f"[write-split-q42-cancel] {wrapper_path} record={record_index} pair=({q},{q2})", file=sys.stderr)
            return True

        if not disable_q42_cancel and emit_q42_cancel_split_record():
            return

        term_modules: dict[tuple[int, int], str] = {}
        if not inline_row_parts:
            for g in divs_q:
                for h in divs_q2:
                    term_stem = f"{stem}Term_{g}_{h}"
                    term_path = os.path.join(out_dir, f"{term_stem}.lean")
                    term_modules[(g, h)] = lean_module_name_for_path(term_path)
                    with open(term_path, "w", encoding="utf-8") as fh:
                        emit_header(fh, [base_import])
                        print(f"theorem {name}_term_{g}_{h} :", file=fh)
                        for line in term_expr_lines(q, q2, g, h, indent="    "):
                            print(line, file=fh)
                        print(f"      = {fraction_to_q_literal(term_values[(g, h)])} := by", file=fh)
                        if term_values[(g, h)] != 0:
                            print(f"  have hCoeffLeft : ramanujanGcdClassCoeffRat {q} {g} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q][g])} := by", file=fh)
                            print("    native_decide", file=fh)
                            print(f"  have hCoeffRight : ramanujanGcdClassCoeffRat {q2} {h} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q2][h])} := by", file=fh)
                            print("    native_decide", file=fh)
                            print(f"  have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 {q} {g} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q][g])} := by", file=fh)
                            print("    native_decide", file=fh)
                            print(f"  have hAvgRight : ramanujanGcdClassWindowAverageRat X0 {q2} {h} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q2][h])} := by", file=fh)
                            print("    native_decide", file=fh)
                            for line in emit_block_periodic_count_proof(theorem_name="hBlockLeft", q=q, q2=q2, q0=q, g0=g, expected=block_left_values[g]):
                                print(line, file=fh)
                            for line in emit_block_periodic_count_proof(theorem_name="hBlockRight", q=q, q2=q2, q0=q2, g0=h, expected=block_right_values[h]):
                                print(line, file=fh)
                            for line in emit_pair_resolved_count_proof(theorem_name="hPair", q=q, q2=q2, g=g, h=h, expected=pair_values[(g, h)]):
                                print(line, file=fh)
                            print("  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,", file=fh)
                            print("    hCoeffLeft, hCoeffRight, hAvgLeft, hAvgRight,", file=fh)
                            print("    hBlockLeft, hBlockRight, hPair]", file=fh)
                        elif can_use_right_odd_structural_zero(q2, g, h):
                            for line in emit_right_odd_structural_zero_proofs(q=q, q2=q2, g=g, h=h):
                                print(line, file=fh)
                            print("  rw [hPair, hAvgRight, hBlockRight]", file=fh)
                            print("  simp", file=fh)
                        elif can_use_left_odd_structural_zero(q, g):
                            for line in emit_left_odd_structural_zero_proofs(q=q, q2=q2, g=g, h=h, expected_pair=pair_values[(g, h)]):
                                print(line, file=fh)
                            print("  rw [hPair, hAvgLeft, hBlockLeft]", file=fh)
                            print("  simp", file=fh)
                        else:
                            print(f"  have hCoeffLeft : ramanujanGcdClassCoeffRat {q} {g} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q][g])} := by", file=fh)
                            print("    native_decide", file=fh)
                            print(f"  have hCoeffRight : ramanujanGcdClassCoeffRat {q2} {h} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q2][h])} := by", file=fh)
                            print("    native_decide", file=fh)
                            print(f"  have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 {q} {g} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q][g])} := by", file=fh)
                            print("    native_decide", file=fh)
                            print(f"  have hAvgRight : ramanujanGcdClassWindowAverageRat X0 {q2} {h} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q2][h])} := by", file=fh)
                            print("    native_decide", file=fh)
                            for line in emit_block_periodic_count_proof(theorem_name="hBlockLeft", q=q, q2=q2, q0=q, g0=g, expected=block_left_values[g]):
                                print(line, file=fh)
                            for line in emit_block_periodic_count_proof(theorem_name="hBlockRight", q=q, q2=q2, q0=q2, g0=h, expected=block_right_values[h]):
                                print(line, file=fh)
                            for line in emit_pair_resolved_count_proof(theorem_name="hPair", q=q, q2=q2, g=g, h=h, expected=pair_values[(g, h)]):
                                print(line, file=fh)
                            print("  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,", file=fh)
                            print("    hCoeffLeft, hCoeffRight, hAvgLeft, hAvgRight,", file=fh)
                            print("    hBlockLeft, hBlockRight, hPair]", file=fh)
                        print(file=fh)
                        emit_footer(fh)

        row_modules: dict[int, str] = {}
        for g in divs_q:
            chunks = [divs_q2[i:i + row_part_size] for i in range(0, len(divs_q2), row_part_size)]
            chunk_names: list[str] = []
            part_modules: list[str] = []
            for part_idx, chunk in enumerate(chunks):
                part_stem = f"{stem}Row_{g}Part{part_idx}"
                part_path = os.path.join(out_dir, f"{part_stem}.lean")
                part_modules.append(lean_module_name_for_path(part_path))
                chunk_name = f"{name}_rowChunk_{g}_{part_idx}"
                chunk_names.append(chunk_name)
                imports = [base_import] if inline_row_parts else [term_modules[(g, h)] for h in chunk]
                part_total = sum((term_values[(g, h)] for h in chunk), Fraction(0, 1))
                with open(part_path, "w", encoding="utf-8") as fh:
                    emit_header(fh, imports)
                    print(f"def {chunk_name} : Finset ℕ :=", file=fh)
                    print(f"  ({lean_nat_list(chunk)} : List ℕ).toFinset", file=fh)
                    print(file=fh)
                    print(f"def {name}_rowPartValue_{g}_{part_idx} : ℕ → ℚ", file=fh)
                    for h in chunk:
                        print(f"| {h} => {fraction_to_q_literal(term_values[(g, h)])}", file=fh)
                    print("| _ => 0", file=fh)
                    print(file=fh)
                    print(f"theorem {name}_rowPart_{g}_{part_idx} :", file=fh)
                    print(f"    (∑ h ∈ {chunk_name},", file=fh)
                    for line in term_expr_lines(q, q2, g, "h", indent="      "):
                        print(line, file=fh)
                    print(f"    ) = {fraction_to_q_literal(part_total)} := by", file=fh)
                    print("  have hsum :", file=fh)
                    print(f"      (∑ h ∈ {chunk_name},", file=fh)
                    for line in term_expr_lines(q, q2, g, "h", indent="        "):
                        print(line, file=fh)
                    print(f"      ) = (∑ h ∈ {chunk_name}, {name}_rowPartValue_{g}_{part_idx} h) := by", file=fh)
                    print("    apply Finset.sum_congr rfl", file=fh)
                    print("    intro h hh", file=fh)
                    print(f"    simp [{chunk_name}] at hh", file=fh)
                    print("    rcases hh with " + " | ".join(["rfl"] * len(chunk)), file=fh)
                    for h in chunk:
                        if inline_row_parts:
                            print("    · have hTerm :", file=fh)
                            for line in term_expr_lines(q, q2, g, h, indent="          "):
                                print(line, file=fh)
                            print(f"          = {fraction_to_q_literal(term_values[(g, h)])} := by", file=fh)
                            if term_values[(g, h)] == 0:
                                if can_use_right_odd_structural_zero(q2, g, h):
                                    for line in emit_right_odd_structural_zero_proofs(q=q, q2=q2, g=g, h=h, indent="        "):
                                        print(line, file=fh)
                                    print("        rw [hPair, hAvgRight, hBlockRight]", file=fh)
                                    print("        simp", file=fh)
                                elif can_use_left_odd_structural_zero(q, g):
                                    for line in emit_left_odd_structural_zero_proofs(q=q, q2=q2, g=g, h=h, expected_pair=pair_values[(g, h)], indent="        "):
                                        print(line, file=fh)
                                    print("        rw [hPair, hAvgLeft, hBlockLeft]", file=fh)
                                    print("        simp", file=fh)
                                else:
                                    print(f"        have hCoeffLeft : ramanujanGcdClassCoeffRat {q} {g} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q][g])} := by", file=fh)
                                    print("          native_decide", file=fh)
                                    print(f"        have hCoeffRight : ramanujanGcdClassCoeffRat {q2} {h} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q2][h])} := by", file=fh)
                                    print("          native_decide", file=fh)
                                    print(f"        have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 {q} {g} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q][g])} := by", file=fh)
                                    print("          native_decide", file=fh)
                                    print(f"        have hAvgRight : ramanujanGcdClassWindowAverageRat X0 {q2} {h} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q2][h])} := by", file=fh)
                                    print("          native_decide", file=fh)
                                    for line in emit_block_periodic_count_proof(theorem_name="hBlockLeft", q=q, q2=q2, q0=q, g0=g, expected=block_left_values[g], indent="        "):
                                        print(line, file=fh)
                                    for line in emit_block_periodic_count_proof(theorem_name="hBlockRight", q=q, q2=q2, q0=q2, g0=h, expected=block_right_values[h], indent="        "):
                                        print(line, file=fh)
                                    for line in emit_pair_resolved_count_proof(theorem_name="hPair", q=q, q2=q2, g=g, h=h, expected=pair_values[(g, h)], indent="        "):
                                        print(line, file=fh)
                                    print("        norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,", file=fh)
                                    print("          hCoeffLeft, hCoeffRight, hAvgLeft, hAvgRight,", file=fh)
                                    print("          hBlockLeft, hBlockRight, hPair]", file=fh)
                            else:
                                print(f"        have hCoeffLeft : ramanujanGcdClassCoeffRat {q} {g} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q][g])} := by", file=fh)
                                print("          native_decide", file=fh)
                                print(f"        have hCoeffRight : ramanujanGcdClassCoeffRat {q2} {h} = {fraction_to_q_literal(exact_ctx['gcd_coeff_by_q'][q2][h])} := by", file=fh)
                                print("          native_decide", file=fh)
                                print(f"        have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 {q} {g} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q][g])} := by", file=fh)
                                print("          native_decide", file=fh)
                                print(f"        have hAvgRight : ramanujanGcdClassWindowAverageRat X0 {q2} {h} = {fraction_to_q_literal(exact_ctx['avg_by_q'][q2][h])} := by", file=fh)
                                print("          native_decide", file=fh)
                                for line in emit_block_periodic_count_proof(theorem_name="hBlockLeft", q=q, q2=q2, q0=q, g0=g, expected=block_left_values[g], indent="        "):
                                    print(line, file=fh)
                                for line in emit_block_periodic_count_proof(theorem_name="hBlockRight", q=q, q2=q2, q0=q2, g0=h, expected=block_right_values[h], indent="        "):
                                    print(line, file=fh)
                                for line in emit_pair_resolved_count_proof(theorem_name="hPair", q=q, q2=q2, g=g, h=h, expected=pair_values[(g, h)], indent="        "):
                                    print(line, file=fh)
                                print("        norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,", file=fh)
                                print("          hCoeffLeft, hCoeffRight, hAvgLeft, hAvgRight,", file=fh)
                                print("          hBlockLeft, hBlockRight, hPair]", file=fh)
                            print(f"      simpa [{name}_rowPartValue_{g}_{part_idx}] using hTerm", file=fh)
                        else:
                            print(f"    · simpa [{name}_rowPartValue_{g}_{part_idx}] using {name}_term_{g}_{h}", file=fh)
                    print("  rw [hsum]", file=fh)
                    print(f"  norm_num [{chunk_name}, {name}_rowPartValue_{g}_{part_idx}]", file=fh)
                    print(file=fh)
                    emit_footer(fh)

            row_stem = f"{stem}Row_{g}"
            row_path = os.path.join(out_dir, f"{row_stem}.lean")
            row_modules[g] = lean_module_name_for_path(row_path)
            with open(row_path, "w", encoding="utf-8") as fh:
                emit_header(fh, part_modules)
                print(f"theorem {name}_divRight_for_row_{g} : Nat.divisors {q2} = ({lean_nat_list(divs_q2)} : List ℕ).toFinset := by", file=fh)
                print("  decide", file=fh)
                print(file=fh)
                print(f"theorem {name}_row_{g} :", file=fh)
                print(f"    (∑ h ∈ Nat.divisors {q2},", file=fh)
                for line in term_expr_lines(q, q2, g, "h", indent="      "):
                    print(line, file=fh)
                print(f"    ) = {fraction_to_q_literal(row_values[g])} := by", file=fh)
                print(f"  rw [{name}_divRight_for_row_{g}]", file=fh)
                union_expr = split_union_expr(chunk_names)
                print(f"  have hset : ({lean_nat_list(divs_q2)} : List ℕ).toFinset = {union_expr} := by", file=fh)
                print("    native_decide", file=fh)
                print("  rw [hset]", file=fh)
                for split_idx in range(len(chunk_names) - 1, 0, -1):
                    left = split_union_expr(chunk_names, split_idx)
                    right = chunk_names[split_idx]
                    print(f"  rw [Finset.sum_union (by native_decide : Disjoint {left} {right})]", file=fh)
                part_theorems = [f"{name}_rowPart_{g}_{idx}" for idx in range(len(chunk_names))]
                print("  rw [" + ", ".join(part_theorems) + "]", file=fh)
                if len(chunk_names) > 1:
                    print("  norm_num", file=fh)
                print(file=fh)
                emit_footer(fh)

        with open(wrapper_path, "w", encoding="utf-8") as fh:
            emit_header(fh, [row_modules[g] for g in divs_q])
            record_kind = "zero-record" if expected == 0 else "nonzero-record"
            print(f"/- Split generated periodic-main {record_kind} proof for selected JSON index {record_index}. -/", file=fh)
            print(file=fh)
            print(f"theorem {name}_divLeft : Nat.divisors {q} = ({lean_nat_list(divs_q)} : List ℕ).toFinset := by", file=fh)
            print("  decide", file=fh)
            print(file=fh)
            print(f"def {name}_rowValue : ℕ → ℚ", file=fh)
            for g in divs_q:
                print(f"| {g} => {fraction_to_q_literal(row_values[g])}", file=fh)
            print("| _ => 0", file=fh)
            print(file=fh)
            print(f"theorem {name}_centeredTerm :", file=fh)
            print(f"    centeredRamanujanPairPeriodicMainTermRat X0 {q} {q2} = {fraction_to_q_literal(centered_term)} := by", file=fh)
            print("  unfold centeredRamanujanPairPeriodicMainTermRat", file=fh)
            print("  have hsum :", file=fh)
            print(f"      (∑ g ∈ Nat.divisors {q}, ∑ h ∈ Nat.divisors {q2},", file=fh)
            for line in term_expr_lines(q, q2, "g", "h", indent="        "):
                print(line, file=fh)
            print(f"      ) = (∑ g ∈ Nat.divisors {q}, {name}_rowValue g) := by", file=fh)
            print("    apply Finset.sum_congr rfl", file=fh)
            print("    intro g hg", file=fh)
            print(f"    rw [{name}_divLeft] at hg", file=fh)
            print("    simp at hg", file=fh)
            print("    rcases hg with " + " | ".join(["rfl"] * len(divs_q)), file=fh)
            for g in divs_q:
                print(f"    · simpa [{name}_rowValue] using {name}_row_{g}", file=fh)
            print(f"  rw [hsum, {name}_divLeft]", file=fh)
            print(f"  norm_num [{name}_rowValue]", file=fh)
            print(file=fh)
            print(f"theorem {name}_orderedSummand :", file=fh)
            print(f"    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk {q} {q2}) = {fraction_to_q_literal(summand_value)} := by", file=fh)
            print(f"  have hneq : {q} ≠ {q2} := by", file=fh)
            print("    norm_num", file=fh)
            print(f"  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat {q} = {fraction_to_q_literal(coeff_q)} := by", file=fh)
            print("    native_decide", file=fh)
            print(f"  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat {q2} = {fraction_to_q_literal(coeff_q2)} := by", file=fh)
            print("    native_decide", file=fh)
            print(
                f"  have hvalue : ({fraction_to_q_literal(coeff_q)}) * ({fraction_to_q_literal(coeff_q2)}) "
                f"* ({fraction_to_q_literal(centered_term)}) = {fraction_to_q_literal(summand_value)} := by",
                file=fh,
            )
            print("    norm_num", file=fh)
            print("  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue", file=fh)
            print("    hneq hCoeffLeft hCoeffRight", file=fh)
            print(f"    {name}_centeredTerm", file=fh)
            print("    hvalue", file=fh)
            print(file=fh)
            with contextlib.redirect_stdout(fh):
                if expected == 0:
                    emit_periodic_main_zero_record_batch_wrapper(X=X, label=label, records=[record])
                else:
                    emit_periodic_main_record_batch_wrapper(X=X, label=label, records=[record])
            emit_footer(fh)
        print(f"[write-split] {wrapper_path} record={record_index} pair=({q},{q2})", file=sys.stderr)

    for local_index, record in enumerate(records):
        emit_split_record(record, index_offset + local_index)
    return len(records)


def emit_periodic_main_zero_value_chunk_assembly_lean(
    *,
    target_set_name: str,
    assembly_set_name: str,
    theorem_name: str,
    module_prefix: str,
    label_prefix: str,
    chunk_count: int,
    extra_imports: list[str] | None = None,
) -> None:
    if chunk_count <= 0:
        raise SystemExit("--emit-periodic-main-zero-value-chunk-assembly-lean requires CHUNK_COUNT > 0")
    labels = [f"{label_prefix}{idx:03d}" for idx in range(chunk_count)]
    modules = [f"{module_prefix}{idx:03d}" for idx in range(chunk_count)]
    imports = [
        "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit",
        *(extra_imports or []),
        *modules,
    ]
    emit_periodic_main_pair_primitive_lean_header(imports=imports)
    print("/- Generated assembly for zero-record value-on-record chunk payloads. -/")
    print()
    print(f"def {assembly_set_name} : Finset (ℕ × ℕ) :=")
    union_expr = f"PeriodicMainRecords{labels[0]}Pairs"
    for label in labels[1:]:
        union_expr = f"({union_expr} ∪ PeriodicMainRecords{label}Pairs)"
    print(f"  {union_expr}")
    print()
    print(f"theorem {assembly_set_name}_eq_target :")
    print(f"    {assembly_set_name} = {target_set_name} := by")
    print("  native_decide")
    print()
    print(f"theorem {theorem_name} :")
    print(f"    ∀ p ∈ {target_set_name},")
    print("      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by")
    print("  intro p hp")
    print(f"  have hpPayload : p ∈ {assembly_set_name} := by")
    print(f"    simpa [{assembly_set_name}_eq_target] using hp")
    if chunk_count == 1:
      print(f"  simp only [{assembly_set_name}] at hpPayload")
      print(f"  exact PeriodicMainRecords{labels[0]}_value_on_records p hpPayload")
    else:
      print(f"  simp only [{assembly_set_name}, Finset.mem_union] at hpPayload")
      rcases_pattern = left_assoc_or_pattern([f"h{idx}" for idx in range(chunk_count)])
      print(f"  rcases hpPayload with {rcases_pattern}")
      for idx, label in enumerate(labels):
          print(f"  · exact PeriodicMainRecords{label}_value_on_records p h{idx}")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_zero_value_chunk_group_lean(
    *,
    group_set_name: str,
    theorem_name: str,
    module_prefix: str,
    label_prefix: str,
    start_index: int,
    chunk_count: int,
    extra_imports: list[str] | None = None,
) -> None:
    if start_index < 0:
        raise SystemExit("START_INDEX must be nonnegative")
    if chunk_count <= 0:
        raise SystemExit("CHUNK_COUNT must be positive")
    indices = list(range(start_index, start_index + chunk_count))
    labels = [f"{label_prefix}{idx:03d}" for idx in indices]
    modules = [f"{module_prefix}{idx:03d}" for idx in indices]
    imports = [
        "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit",
        *(extra_imports or []),
        *modules,
    ]
    emit_periodic_main_pair_primitive_lean_header(imports=imports)
    print("/- Generated group assembly for zero-record value-on-record chunk payloads. -/")
    print()
    print(f"def {group_set_name} : Finset (ℕ × ℕ) :=")
    union_expr = f"PeriodicMainRecords{labels[0]}Pairs"
    for label in labels[1:]:
        union_expr = f"({union_expr} ∪ PeriodicMainRecords{label}Pairs)"
    print(f"  {union_expr}")
    print()
    print(f"theorem {theorem_name} :")
    print(f"    ∀ p ∈ {group_set_name},")
    print("      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by")
    print("  intro p hp")
    if chunk_count == 1:
        print(f"  simp only [{group_set_name}] at hp")
        print(f"  exact PeriodicMainRecords{labels[0]}_value_on_records p hp")
    else:
        print(f"  simp only [{group_set_name}, Finset.mem_union] at hp")
        rcases_pattern = left_assoc_or_pattern([f"h{idx}" for idx in range(chunk_count)])
        print(f"  rcases hp with {rcases_pattern}")
        for idx, label in enumerate(labels):
            print(f"  · exact PeriodicMainRecords{label}_value_on_records p h{idx}")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_zero_value_grouped_final_lean(
    *,
    target_set_name: str,
    assembly_set_name: str,
    theorem_name: str,
    group_module_prefix: str,
    group_set_prefix: str,
    group_set_suffix: str,
    group_theorem_prefix: str,
    group_theorem_suffix: str,
    group_count: int,
    extra_imports: list[str] | None = None,
) -> None:
    if group_count <= 0:
        raise SystemExit("GROUP_COUNT must be positive")
    group_sets = [f"{group_set_prefix}{idx:03d}{group_set_suffix}" for idx in range(group_count)]
    group_theorems = [f"{group_theorem_prefix}{idx:03d}{group_theorem_suffix}" for idx in range(group_count)]
    group_modules = [f"{group_module_prefix}{idx:03d}" for idx in range(group_count)]
    imports = [
        "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit",
        *(extra_imports or []),
        *group_modules,
    ]
    emit_periodic_main_pair_primitive_lean_header(imports=imports)
    print("/- Generated final grouped assembly for zero-record value-on-record payloads. -/")
    print()
    print(f"def {assembly_set_name} : Finset (ℕ × ℕ) :=")
    union_expr = group_sets[0]
    for group_set in group_sets[1:]:
        union_expr = f"({union_expr} ∪ {group_set})"
    print(f"  {union_expr}")
    print()
    print(f"theorem {assembly_set_name}_eq_target :")
    print(f"    {assembly_set_name} = {target_set_name} := by")
    print("  native_decide")
    print()
    print(f"theorem {theorem_name} :")
    print(f"    ∀ p ∈ {target_set_name},")
    print("      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by")
    print("  intro p hp")
    print(f"  have hpPayload : p ∈ {assembly_set_name} := by")
    print(f"    simpa [{assembly_set_name}_eq_target] using hp")
    if group_count == 1:
        print(f"  simp only [{assembly_set_name}] at hpPayload")
        print(f"  exact {group_theorems[0]} p hpPayload")
    else:
        print(f"  simp only [{assembly_set_name}, Finset.mem_union] at hpPayload")
        rcases_pattern = left_assoc_or_pattern([f"h{idx}" for idx in range(group_count)])
        print(f"  rcases hpPayload with {rcases_pattern}")
        for idx, group_theorem in enumerate(group_theorems):
            print(f"  · exact {group_theorem} p h{idx}")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_nonzero_value_chunk_group_lean(
    *,
    group_set_name: str,
    group_total_name: str,
    theorem_name: str,
    module_prefix: str,
    label_prefix: str,
    start_index: int,
    chunk_count: int,
    extra_imports: list[str] | None = None,
) -> None:
    if start_index < 0:
        raise SystemExit("START_INDEX must be nonnegative")
    if chunk_count <= 0:
        raise SystemExit("CHUNK_COUNT must be positive")
    indices = list(range(start_index, start_index + chunk_count))
    labels = [f"{label_prefix}{idx:03d}" for idx in indices]
    modules = [f"{module_prefix}{idx:03d}" for idx in indices]
    imports = [
        "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainReducedSparse",
        *(extra_imports or []),
        *modules,
    ]
    emit_periodic_main_pair_primitive_lean_header(imports=imports)
    print("/- Generated group assembly for nonzero-record value chunk payloads. -/")
    print()

    actual = "surrogatePeriodicMainActiveOrderedPairSummandRat X0"
    for label in labels:
        print(f"theorem PeriodicMainRecords{label}_actual_sum :")
        print(f"    (∑ p ∈ PeriodicMainRecords{label}Pairs, {actual} p) =")
        print(f"      PeriodicMainRecords{label}Total := by")
        print("  calc")
        print(f"    (∑ p ∈ PeriodicMainRecords{label}Pairs, {actual} p)")
        print(f"        = (∑ p ∈ PeriodicMainRecords{label}Pairs, PeriodicMainRecords{label}Value p) := by")
        print("          refine Finset.sum_congr rfl ?_")
        print("          intro p hp")
        print(f"          simpa [PeriodicMainRecords{label}Value] using PeriodicMainRecords{label}_value_on_records p hp")
        print(f"    _ = PeriodicMainRecords{label}Total := PeriodicMainRecords{label}_records_sum")
        print()

    upto_sets = [f"{group_set_name}UpTo{idx:03d}" for idx in range(chunk_count)]
    upto_totals = [f"{group_total_name}UpTo{idx:03d}" for idx in range(chunk_count)]
    for local_idx, label in enumerate(labels):
        set_name = upto_sets[local_idx]
        total_name = upto_totals[local_idx]
        if local_idx == 0:
            print(f"def {set_name} : Finset (ℕ × ℕ) :=")
            print(f"  PeriodicMainRecords{label}Pairs")
            print()
            print(f"def {total_name} : ℚ :=")
            print(f"  PeriodicMainRecords{label}Total")
            print()
            print(f"theorem {set_name}_actual_sum :")
            print(f"    (∑ p ∈ {set_name}, {actual} p) = {total_name} := by")
            print(f"  simpa [{set_name}, {total_name}] using PeriodicMainRecords{label}_actual_sum")
            print()
        else:
            prev_set = upto_sets[local_idx - 1]
            prev_total = upto_totals[local_idx - 1]
            print(f"def {set_name} : Finset (ℕ × ℕ) :=")
            print(f"  {prev_set} ∪ PeriodicMainRecords{label}Pairs")
            print()
            print(f"def {total_name} : ℚ :=")
            print(f"  {prev_total} + PeriodicMainRecords{label}Total")
            print()
            print(f"theorem {prev_set}_disjoint_PeriodicMainRecords{label}Pairs :")
            print(f"    Disjoint {prev_set} PeriodicMainRecords{label}Pairs := by")
            print("  native_decide")
            print()
            print(f"theorem {set_name}_actual_sum :")
            print(f"    (∑ p ∈ {set_name}, {actual} p) = {total_name} := by")
            print(f"  rw [{set_name}, Finset.sum_union {prev_set}_disjoint_PeriodicMainRecords{label}Pairs]")
            print(f"  rw [{prev_set}_actual_sum, PeriodicMainRecords{label}_actual_sum]")
            print(f"  rfl")
            print()

    print(f"def {group_set_name} : Finset (ℕ × ℕ) :=")
    print(f"  {upto_sets[-1]}")
    print()
    print(f"def {group_total_name} : ℚ :=")
    print(f"  {upto_totals[-1]}")
    print()
    print(f"theorem {theorem_name} :")
    print(f"    (∑ p ∈ {group_set_name}, {actual} p) = {group_total_name} := by")
    print(f"  simpa [{group_set_name}, {group_total_name}] using {upto_sets[-1]}_actual_sum")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_nonzero_value_grouped_final_lean(
    *,
    target_set_name: str,
    assembly_set_name: str,
    assembly_total_name: str,
    theorem_name: str,
    group_module_prefix: str,
    group_set_prefix: str,
    group_total_prefix: str,
    group_theorem_prefix: str,
    group_count: int,
    extra_imports: list[str] | None = None,
) -> None:
    if group_count <= 0:
        raise SystemExit("GROUP_COUNT must be positive")
    group_sets = [f"{group_set_prefix}{idx:03d}Pairs" for idx in range(group_count)]
    group_totals = [f"{group_total_prefix}{idx:03d}Total" for idx in range(group_count)]
    group_theorems = [f"{group_theorem_prefix}{idx:03d}_actual_sum" for idx in range(group_count)]
    group_modules = [f"{group_module_prefix}{idx:03d}" for idx in range(group_count)]
    imports = [
        "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainReducedSparse",
        *(extra_imports or []),
        *group_modules,
    ]
    emit_periodic_main_pair_primitive_lean_header(imports=imports)
    print("/- Generated final grouped assembly for nonzero-record value payloads. -/")
    print()

    actual = "surrogatePeriodicMainActiveOrderedPairSummandRat X0"
    upto_sets = [f"{assembly_set_name}UpTo{idx:03d}" for idx in range(group_count)]
    upto_totals = [f"{assembly_total_name}UpTo{idx:03d}" for idx in range(group_count)]
    for idx in range(group_count):
        if idx == 0:
            print(f"def {upto_sets[idx]} : Finset (ℕ × ℕ) :=")
            print(f"  {group_sets[idx]}")
            print()
            print(f"def {upto_totals[idx]} : ℚ :=")
            print(f"  {group_totals[idx]}")
            print()
            print(f"theorem {upto_sets[idx]}_actual_sum :")
            print(f"    (∑ p ∈ {upto_sets[idx]}, {actual} p) = {upto_totals[idx]} := by")
            print(f"  simpa [{upto_sets[idx]}, {upto_totals[idx]}] using {group_theorems[idx]}")
            print()
        else:
            prev_set = upto_sets[idx - 1]
            prev_total = upto_totals[idx - 1]
            print(f"def {upto_sets[idx]} : Finset (ℕ × ℕ) :=")
            print(f"  {prev_set} ∪ {group_sets[idx]}")
            print()
            print(f"def {upto_totals[idx]} : ℚ :=")
            print(f"  {prev_total} + {group_totals[idx]}")
            print()
            print(f"theorem {prev_set}_disjoint_{group_sets[idx]} :")
            print(f"    Disjoint {prev_set} {group_sets[idx]} := by")
            print("  native_decide")
            print()
            print(f"theorem {upto_sets[idx]}_actual_sum :")
            print(f"    (∑ p ∈ {upto_sets[idx]}, {actual} p) = {upto_totals[idx]} := by")
            print(f"  rw [{upto_sets[idx]}, Finset.sum_union {prev_set}_disjoint_{group_sets[idx]}]")
            print(f"  rw [{prev_set}_actual_sum, {group_theorems[idx]}]")
            print(f"  rfl")
            print()

    print(f"def {assembly_set_name} : Finset (ℕ × ℕ) :=")
    print(f"  {upto_sets[-1]}")
    print()
    print(f"def {assembly_total_name} : ℚ :=")
    print(f"  {upto_totals[-1]}")
    print()
    print(f"theorem {assembly_set_name}_eq_target :")
    print(f"    {assembly_set_name} = {target_set_name} := by")
    print("  native_decide")
    print()
    print(f"theorem {assembly_set_name}_actual_sum :")
    print(f"    (∑ p ∈ {assembly_set_name}, {actual} p) = {assembly_total_name} := by")
    print(f"  simpa [{assembly_set_name}, {assembly_total_name}] using {upto_sets[-1]}_actual_sum")
    print()
    print(f"theorem {theorem_name} :")
    print(f"    (∑ p ∈ {target_set_name}, {actual} p) = surrogatePeriodicMainX0RatCert := by")
    print(f"  rw [← {assembly_set_name}_eq_target]")
    print(f"  rw [{assembly_set_name}_actual_sum]")
    numeric_defs = ", ".join(
        ["surrogatePeriodicMainX0RatCert", assembly_total_name]
        + upto_totals
        + group_totals
    )
    print(f"  norm_num [{numeric_defs}]")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_row_value_chunk_group_lean(
    *,
    group_set_name: str,
    group_total_name: str,
    theorem_name: str,
    module_prefix: str,
    label_prefix: str,
    start_index: int,
    chunk_count: int,
    extra_imports: list[str] | None = None,
) -> None:
    if start_index < 0:
        raise SystemExit("START_INDEX must be nonnegative")
    if chunk_count <= 0:
        raise SystemExit("CHUNK_COUNT must be positive")
    indices = list(range(start_index, start_index + chunk_count))
    labels = [f"{label_prefix}{idx:03d}" for idx in indices]
    modules = [f"{module_prefix}{idx:03d}" for idx in indices]
    imports = [
        *(extra_imports or []),
        *modules,
    ]
    emit_periodic_main_pair_primitive_lean_header(imports=imports)
    print("/- Generated row-local actual-sum theorem over periodic-main record modules. -/")
    print()

    actual = "surrogatePeriodicMainActiveOrderedPairSummandRat X0"
    for label in labels:
        print(f"theorem PeriodicMainRecords{label}_actual_sum :")
        print(f"    (∑ p ∈ PeriodicMainRecords{label}Pairs, {actual} p) =")
        print(f"      PeriodicMainRecords{label}Total := by")
        print("  calc")
        print(f"    (∑ p ∈ PeriodicMainRecords{label}Pairs, {actual} p)")
        print(f"        = (∑ p ∈ PeriodicMainRecords{label}Pairs, PeriodicMainRecords{label}Value p) := by")
        print("          refine Finset.sum_congr rfl ?_")
        print("          intro p hp")
        print(f"          simpa [PeriodicMainRecords{label}Value] using PeriodicMainRecords{label}_value_on_records p hp")
        print(f"    _ = PeriodicMainRecords{label}Total := PeriodicMainRecords{label}_records_sum")
        print()

    upto_sets = [f"{group_set_name}UpTo{idx:03d}" for idx in range(chunk_count)]
    upto_totals = [f"{group_total_name}UpTo{idx:03d}" for idx in range(chunk_count)]
    for local_idx, label in enumerate(labels):
        set_name = upto_sets[local_idx]
        total_name = upto_totals[local_idx]
        if local_idx == 0:
            print(f"def {set_name} : Finset (ℕ × ℕ) :=")
            print(f"  PeriodicMainRecords{label}Pairs")
            print()
            print(f"def {total_name} : ℚ :=")
            print(f"  PeriodicMainRecords{label}Total")
            print()
            print(f"theorem {set_name}_actual_sum :")
            print(f"    (∑ p ∈ {set_name}, {actual} p) = {total_name} := by")
            print(f"  simpa [{set_name}, {total_name}] using PeriodicMainRecords{label}_actual_sum")
            print()
        else:
            prev_set = upto_sets[local_idx - 1]
            prev_total = upto_totals[local_idx - 1]
            print(f"def {set_name} : Finset (ℕ × ℕ) :=")
            print(f"  {prev_set} ∪ PeriodicMainRecords{label}Pairs")
            print()
            print(f"def {total_name} : ℚ :=")
            print(f"  {prev_total} + PeriodicMainRecords{label}Total")
            print()
            print(f"theorem {prev_set}_disjoint_PeriodicMainRecords{label}Pairs :")
            print(f"    Disjoint {prev_set} PeriodicMainRecords{label}Pairs := by")
            print("  native_decide")
            print()
            print(f"theorem {set_name}_actual_sum :")
            print(f"    (∑ p ∈ {set_name}, {actual} p) = {total_name} := by")
            print(f"  rw [{set_name}, Finset.sum_union {prev_set}_disjoint_PeriodicMainRecords{label}Pairs]")
            print(f"  rw [{prev_set}_actual_sum, PeriodicMainRecords{label}_actual_sum]")
            print(f"  rfl")
            print()

    print(f"def {group_set_name} : Finset (ℕ × ℕ) :=")
    print(f"  {upto_sets[-1]}")
    print()
    print(f"def {group_total_name} : ℚ :=")
    print(f"  {upto_totals[-1]}")
    print()
    print(f"theorem {theorem_name} :")
    print(f"    (∑ p ∈ {group_set_name}, {actual} p) = {group_total_name} := by")
    print(f"  simpa [{group_set_name}, {group_total_name}] using {upto_sets[-1]}_actual_sum")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_row_value_grouped_final_lean(
    *,
    target_set_name: str,
    target_total_name: str,
    assembly_set_name: str,
    assembly_total_name: str,
    theorem_name: str,
    group_module_prefix: str,
    group_set_prefix: str,
    group_total_prefix: str,
    group_theorem_prefix: str,
    group_count: int,
    extra_imports: list[str] | None = None,
) -> None:
    if group_count <= 0:
        raise SystemExit("GROUP_COUNT must be positive")
    group_sets = [f"{group_set_prefix}{idx:03d}Pairs" for idx in range(group_count)]
    group_totals = [f"{group_total_prefix}{idx:03d}Total" for idx in range(group_count)]
    group_theorems = [f"{group_theorem_prefix}{idx:03d}_actual_sum" for idx in range(group_count)]
    group_modules = [f"{group_module_prefix}{idx:03d}" for idx in range(group_count)]
    imports = [
        *(extra_imports or []),
        *group_modules,
    ]
    emit_periodic_main_pair_primitive_lean_header(imports=imports)
    print("/- Generated row-local final actual-sum theorem from grouped record modules. -/")
    print()

    actual = "surrogatePeriodicMainActiveOrderedPairSummandRat X0"
    upto_sets = [f"{assembly_set_name}UpTo{idx:03d}" for idx in range(group_count)]
    upto_totals = [f"{assembly_total_name}UpTo{idx:03d}" for idx in range(group_count)]
    for idx in range(group_count):
        if idx == 0:
            print(f"def {upto_sets[idx]} : Finset (ℕ × ℕ) :=")
            print(f"  {group_sets[idx]}")
            print()
            print(f"def {upto_totals[idx]} : ℚ :=")
            print(f"  {group_totals[idx]}")
            print()
            print(f"theorem {upto_sets[idx]}_actual_sum :")
            print(f"    (∑ p ∈ {upto_sets[idx]}, {actual} p) = {upto_totals[idx]} := by")
            print(f"  simpa [{upto_sets[idx]}, {upto_totals[idx]}] using {group_theorems[idx]}")
            print()
        else:
            prev_set = upto_sets[idx - 1]
            prev_total = upto_totals[idx - 1]
            print(f"def {upto_sets[idx]} : Finset (ℕ × ℕ) :=")
            print(f"  {prev_set} ∪ {group_sets[idx]}")
            print()
            print(f"def {upto_totals[idx]} : ℚ :=")
            print(f"  {prev_total} + {group_totals[idx]}")
            print()
            print(f"theorem {prev_set}_disjoint_{group_sets[idx]} :")
            print(f"    Disjoint {prev_set} {group_sets[idx]} := by")
            print("  native_decide")
            print()
            print(f"theorem {upto_sets[idx]}_actual_sum :")
            print(f"    (∑ p ∈ {upto_sets[idx]}, {actual} p) = {upto_totals[idx]} := by")
            print(f"  rw [{upto_sets[idx]}, Finset.sum_union {prev_set}_disjoint_{group_sets[idx]}]")
            print(f"  rw [{prev_set}_actual_sum, {group_theorems[idx]}]")
            print(f"  rfl")
            print()

    print(f"def {assembly_set_name} : Finset (ℕ × ℕ) :=")
    print(f"  {upto_sets[-1]}")
    print()
    print(f"def {assembly_total_name} : ℚ :=")
    print(f"  {upto_totals[-1]}")
    print()
    print(f"theorem {assembly_set_name}_eq_target :")
    print(f"    {assembly_set_name} = {target_set_name} := by")
    print("  native_decide")
    print()
    print(f"theorem {assembly_set_name}_actual_sum :")
    print(f"    (∑ p ∈ {assembly_set_name}, {actual} p) = {assembly_total_name} := by")
    print(f"  simpa [{assembly_set_name}, {assembly_total_name}] using {upto_sets[-1]}_actual_sum")
    print()
    print(f"theorem {theorem_name} :")
    print(f"    (∑ p ∈ {target_set_name}, {actual} p) = {target_total_name} := by")
    print(f"  rw [← {assembly_set_name}_eq_target]")
    print(f"  rw [{assembly_set_name}_actual_sum]")
    print("  native_decide")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def filter_periodic_main_records_for_lean(
    records: list[dict[str, object]],
    *,
    left_rows: set[int] | None = None,
    right_rows: set[int] | None = None,
    gcd_values: set[int] | None = None,
    left_div3_filter: str = "any",
    right_div3_filter: str = "any",
    coprime_filter: str = "any",
    exclude_unit_two: bool = False,
) -> list[dict[str, object]]:
    selected: list[dict[str, object]] = []
    left_rows = left_rows or set()
    right_rows = right_rows or set()
    gcd_values = gcd_values or set()
    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        if left_rows and q not in left_rows:
            continue
        if right_rows and q2 not in right_rows:
            continue
        record_gcd = math.gcd(q, q2)
        if gcd_values and record_gcd not in gcd_values:
            continue
        if left_div3_filter == "yes" and q % 3 != 0:
            continue
        if left_div3_filter == "no" and q % 3 == 0:
            continue
        if right_div3_filter == "yes" and q2 % 3 != 0:
            continue
        if right_div3_filter == "no" and q2 % 3 == 0:
            continue
        if exclude_unit_two and (q in {1, 2} or q2 in {1, 2}):
            continue
        if coprime_filter == "coprime" and record_gcd != 1:
            continue
        if coprime_filter == "noncoprime" and record_gcd == 1:
            continue
        selected.append(record)
    return selected


def periodic_main_zero_classification_report(
    *,
    records: list[dict[str, object]],
    nonzero_records: list[dict[str, object]] | None = None,
    exclude_left: set[int] | None = None,
    top: int = 40,
) -> None:
    exclude_left = exclude_left or set()
    selected = [
        record for record in records
        if int(record["q"]) not in exclude_left
    ]
    by_left: Counter[int] = Counter(int(record["q"]) for record in selected)

    def factor_string(n: int) -> str:
        if n <= 1:
            return "1"
        x = n
        parts: list[str] = []
        p = 2
        while p * p <= x:
            if x % p == 0:
                e = 0
                while x % p == 0:
                    x //= p
                    e += 1
                parts.append(f"{p}^{e}" if e > 1 else str(p))
            p += 1 if p == 2 else 2
        if x > 1:
            parts.append(str(x))
        return "*".join(parts)

    print(f"periodic-main zero records: {len(records)}")
    if exclude_left:
        print("excluded left rows:", " ".join(str(q) for q in sorted(exclude_left)))
    print(f"selected records: {len(selected)}")

    if nonzero_records is not None:
        nonzero_by_left: dict[int, list[dict[str, object]]] = defaultdict(list)
        for record in nonzero_records:
            nonzero_by_left[int(record["q"])].append(record)
        dyadic_exception_rows: list[tuple[int, int, int]] = []
        other_rows: list[tuple[int, int, list[dict[str, object]]]] = []
        for q, count in by_left.items():
            row_nonzero = nonzero_by_left.get(q, [])
            dyadic_partners = {2 * q}
            if q % 2 == 0:
                dyadic_partners.add(q // 2)
            if len(row_nonzero) == 1 and int(row_nonzero[0]["q2"]) in dyadic_partners:
                dyadic_exception_rows.append((q, count, int(row_nonzero[0]["q2"])))
            else:
                other_rows.append((q, count, row_nonzero))
        print(
            "dyadic-exception rows:",
            len(dyadic_exception_rows),
            "zero records:",
            sum(count for _, count, _ in dyadic_exception_rows),
        )
        print(
            "non-dyadic residual rows:",
            len(other_rows),
            "zero records:",
            sum(count for _, count, _ in other_rows),
        )
        print("top dyadic-exception rows")
        print("q,zero_count,nonzero_dyadic_partner")
        for q, count, partner in sorted(dyadic_exception_rows, key=lambda item: -item[1])[:top]:
            print(f"{q},{count},{partner}")

    print()
    print("top left rows")
    print("q,count,factorization,first_q2_values,gcd_classes")
    for q, count in by_left.most_common(top):
        row = [record for record in selected if int(record["q"]) == q]
        q2_values = [int(record["q2"]) for record in row[:12]]
        gcd_classes = Counter(math.gcd(q, int(record["q2"])) for record in row)
        gcd_summary = " ".join(f"{g}:{c}" for g, c in gcd_classes.most_common(12))
        q2_summary = " ".join(str(q2) for q2 in q2_values)
        print(f"{q},{count},{factor_string(q)},{q2_summary},{gcd_summary}")

    print()
    print("top product/lcm classes")
    product_classes: Counter[int] = Counter()
    lcm_classes: Counter[int] = Counter()
    for record in selected:
        q = int(record["q"])
        q2 = int(record["q2"])
        product_classes[q * q2] += 1
        lcm_classes[math.lcm(q, q2)] += 1
    print("product,count")
    for product, count in product_classes.most_common(top):
        print(f"{product},{count}")
    print()
    print("lcm,count")
    for lcm_value, count in lcm_classes.most_common(top):
        print(f"{lcm_value},{count}")


def periodic_main_dyadic_zero_mechanism_report(
    *,
    records: list[dict[str, object]],
    top: int = 40,
) -> None:
    """Report cheap structural mechanisms inside dyadic-exception zero records.

    This is intentionally diagnostic rather than theorem-producing: it identifies
    which zero-record families should be attacked by structural lemmas before
    falling back to generated pointwise certificates.
    """
    by_mechanism: Counter[str] = Counter()
    by_gcd: Counter[int] = Counter()
    by_left: Counter[int] = Counter()
    by_left_gcd: Counter[tuple[int, int]] = Counter()
    by_parity_gcd: Counter[tuple[str, int]] = Counter()
    block_scalar_zero = 0
    unit_two_overlap = 0

    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        d = math.gcd(q, q2)
        by_left[q] += 1
        by_gcd[d] += 1
        by_left_gcd[(q, d)] += 1

        period = 2 * math.lcm(q, q2)
        scalar_zero = ((H + 1) // period) == 0
        if q in (1, 2) or q2 in (1, 2):
            mechanism = "unit_two_overlap"
            unit_two_overlap += 1
        elif scalar_zero:
            mechanism = "block_scalar_zero"
            block_scalar_zero += 1
        elif d != 1:
            mechanism = "noncoprime"
        else:
            q_parity = "odd" if q % 2 else "even"
            q2_parity = "odd" if q2 % 2 else "even"
            mechanism = f"coprime_{q_parity}_{q2_parity}"
        by_mechanism[mechanism] += 1

        parity = ("o" if q % 2 else "e") + ("o" if q2 % 2 else "e")
        by_parity_gcd[(parity, d)] += 1

    print(f"dyadic-exception zero records: {len(records)}")
    print(f"unit/two overlap records: {unit_two_overlap}")
    print(f"block-scalar zero records: {block_scalar_zero}")
    print()
    print("mechanism,count")
    for mechanism, count in by_mechanism.most_common():
        print(f"{mechanism},{count}")
    print()
    print("top left rows")
    print("q,count,top_gcd_classes")
    for q, count in by_left.most_common(top):
        gcds = Counter()
        for (q0, d), gcd_count in by_left_gcd.items():
            if q0 == q:
                gcds[d] += gcd_count
        gcd_summary = " ".join(f"{d}:{gcd_count}" for d, gcd_count in gcds.most_common(12))
        print(f"{q},{count},{gcd_summary}")
    print()
    print("top gcd classes")
    print("gcd,count")
    for d, count in by_gcd.most_common(top):
        print(f"{d},{count}")
    print()
    print("top parity/gcd classes")
    print("parity,gcd,count")
    for (parity, d), count in by_parity_gcd.most_common(top):
        print(f"{parity},{d},{count}")
    print()
    print("top non-unit non-scalar residual rows")
    print("q,count,first_q2_values")
    residual_by_left: dict[int, list[int]] = defaultdict(list)
    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        period = 2 * math.lcm(q, q2)
        if q in (1, 2) or q2 in (1, 2):
            continue
        if ((H + 1) // period) == 0:
            continue
        residual_by_left[q].append(q2)
    for q, q2_values in sorted(residual_by_left.items(), key=lambda item: -len(item[1]))[:top]:
        sample = " ".join(str(q2) for q2 in sorted(q2_values)[:16])
        print(f"{q},{len(q2_values)},{sample}")


def periodic_main_dyadic_exception_zero_records(
    *,
    zero_records: list[dict[str, object]],
    nonzero_records: list[dict[str, object]],
    exclude_left: set[int] | None = None,
    symmetric: bool = False,
) -> list[dict[str, object]]:
    exclude_left = exclude_left or set()
    zero_by_left: dict[int, list[dict[str, object]]] = defaultdict(list)
    nonzero_by_left: dict[int, list[dict[str, object]]] = defaultdict(list)
    for record in zero_records:
        q = int(record["q"])
        if q not in exclude_left:
            zero_by_left[q].append(record)
    for record in nonzero_records:
        q = int(record["q"])
        if q not in exclude_left:
            nonzero_by_left[q].append(record)

    dyadic_rows: set[int] = set()
    for q in sorted(zero_by_left):
        row_nonzero = nonzero_by_left.get(q, [])
        dyadic_partners = {2 * q}
        if q % 2 == 0:
            dyadic_partners.add(q // 2)
        if len(row_nonzero) == 1 and int(row_nonzero[0]["q2"]) in dyadic_partners:
            dyadic_rows.add(q)
    selected: list[dict[str, object]] = []
    for q in sorted(zero_by_left):
        row = sorted(zero_by_left[q], key=lambda record: int(record["q2"]))
        for record in row:
            q2 = int(record["q2"])
            if q in dyadic_rows or (symmetric and q2 in dyadic_rows):
                selected.append(record)
    return selected


def emit_periodic_main_dyadic_exception_zero_records_json(
    *,
    zero_payload: dict[str, object],
    nonzero_payload: dict[str, object],
    exclude_left: set[int] | None = None,
    symmetric: bool = False,
) -> dict[str, object]:
    zero_records = list(zero_payload.get("records", []))
    nonzero_records = list(nonzero_payload.get("records", []))
    records = periodic_main_dyadic_exception_zero_records(
        zero_records=zero_records,
        nonzero_records=nonzero_records,
        exclude_left=exclude_left,
        symmetric=symmetric,
    )
    rows = sorted({int(record["q"]) for record in records})
    return {
        "mode": "periodic-main-ordered-zero-records",
        "submode": "symmetric-dyadic-exception-zero-records" if symmetric
          else "dyadic-exception-zero-records",
        "X": zero_payload.get("X"),
        "excluded_left_rows": sorted(exclude_left or set()),
        "row_count": len(rows),
        "record_count": len(records),
        "rows": rows,
        "records": records,
    }


def emit_periodic_main_residual_zero_records_json(
    *,
    zero_payload: dict[str, object],
    remove_payloads: list[dict[str, object]],
    exclude_left: set[int] | None = None,
) -> dict[str, object]:
    exclude_left = exclude_left or set()
    removed_pairs: set[tuple[int, int]] = set()
    for payload in remove_payloads:
        for record in payload.get("records", []):
            removed_pairs.add((int(record["q"]), int(record["q2"])))
    records = [
        record for record in zero_payload.get("records", [])
        if int(record["q"]) not in exclude_left
        and (int(record["q"]), int(record["q2"])) not in removed_pairs
    ]
    rows = sorted({int(record["q"]) for record in records})
    return {
        "mode": "periodic-main-ordered-zero-records",
        "submode": "residual-zero-records",
        "X": zero_payload.get("X"),
        "excluded_left_rows": sorted(exclude_left),
        "removed_payload_count": len(remove_payloads),
        "row_count": len(rows),
        "record_count": len(records),
        "rows": rows,
        "records": records,
    }


def emit_periodic_main_unit_two_zero_records_json(
    *,
    zero_payload: dict[str, object],
    symmetric: bool = False,
) -> dict[str, object]:
    records = []
    for record in zero_payload.get("records", []):
        q = int(record["q"])
        q2 = int(record["q2"])
        if q in {1, 2} or (symmetric and q2 in {1, 2}):
            records.append(record)
    rows = sorted({int(record["q"]) for record in records})
    return {
        "mode": "periodic-main-ordered-zero-records",
        "submode": "symmetric-unit-two-zero-records" if symmetric
          else "unit-two-left-zero-records",
        "X": zero_payload.get("X"),
        "row_count": len(rows),
        "record_count": len(records),
        "rows": rows,
        "records": records,
    }


def emit_periodic_main_pair_finset_def(name: str, records: list[dict[str, object]]) -> None:
    print(f"def {name} : Finset (ℕ × ℕ) :=")
    print("  ([")
    for idx, record in enumerate(records):
        q = int(record["q"])
        q2 = int(record["q2"])
        comma = "," if idx + 1 < len(records) else ""
        print(f"    ({q}, {q2}){comma}")
    print("  ] : List (ℕ × ℕ)).toFinset")
    print()


def emit_periodic_main_pair_finset_def_chunked(
    name: str,
    records: list[dict[str, object]],
    *,
    chunk_size: int = 500,
) -> None:
    chunk_names: list[str] = []
    for chunk_idx, start in enumerate(range(0, len(records), chunk_size)):
        chunk_name = f"{name}Chunk{chunk_idx:03d}"
        chunk_names.append(chunk_name)
        emit_periodic_main_pair_finset_def(chunk_name, records[start:start + chunk_size])
    chunks_name = f"{name}Chunks"
    print(f"def {chunks_name} : List (Finset (ℕ × ℕ)) :=")
    print("  [")
    for idx, chunk_name in enumerate(chunk_names):
        comma = "," if idx + 1 < len(chunk_names) else ""
        print(f"    {chunk_name}{comma}")
    print("  ]")
    print()
    print(f"def {name} : Finset (ℕ × ℕ) :=")
    print(f"  {chunks_name}.foldl (fun acc s => acc ∪ s) ∅")
    print()


def emit_periodic_main_pair_support_proof_lines(q: int, q2: int, *, indent: str = "  ") -> None:
    print(f"{indent}have hqCoeff : {q} ∈ PeriodicMainCoeffSupportExplicit := by")
    print(f"{indent}  unfold PeriodicMainCoeffSupportExplicit")
    print(f"{indent}  exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩")
    print(f"{indent}have hq2Coeff : {q2} ∈ PeriodicMainCoeffSupportExplicit := by")
    print(f"{indent}  unfold PeriodicMainCoeffSupportExplicit")
    print(f"{indent}  exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩")
    print(f"{indent}have hqActive : {q} ∈ PeriodicMainActiveSupportExplicit := by")
    print(f"{indent}  unfold PeriodicMainActiveSupportExplicit")
    print(f"{indent}  exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩")
    print(f"{indent}have hq2Active : {q2} ∈ PeriodicMainActiveSupportExplicit := by")
    print(f"{indent}  unfold PeriodicMainActiveSupportExplicit")
    print(f"{indent}  exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩")
    print(f"{indent}unfold PeriodicMainFullBlockOrderedPairSupportExplicit")
    print(f"{indent}exact Finset.mem_filter.mpr ⟨by")
    print(f"{indent}  unfold PeriodicMainActiveOrderedPairSupportExplicit")
    print(f"{indent}  exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,")
    print(f"{indent}  by")
    print(f"{indent}    constructor")
    print(f"{indent}    · norm_num")
    print(f"{indent}    · norm_num [centeredRamanujanPairBlockPeriod, H]")
    print(f"{indent}⟩")


def emit_periodic_main_chunk_subset_full_proof(
    *,
    chunk_name: str,
    chunk_records: list[dict[str, object]],
) -> None:
    print(f"theorem {chunk_name}_subset_fullBlockExplicit :")
    print(f"    {chunk_name} ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by")
    print("  intro p hp")
    print(f"  simp [{chunk_name}] at hp")
    print("  rcases hp with " + " | ".join("h" for _ in chunk_records))
    for record in chunk_records:
        q = int(record["q"])
        q2 = int(record["q2"])
        print("  · subst p")
        emit_periodic_main_pair_support_proof_lines(q, q2, indent="    ")
    print()
    print(f"theorem {chunk_name}_subset_fullBlockSquarefreeExplicit :")
    print(f"    {chunk_name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
    print("  intro p hp")
    print("  rw [← PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]")
    print(f"  exact {chunk_name}_subset_fullBlockExplicit hp")
    print()


def emit_periodic_main_record_set_certificate(
    name: str,
    records: list[dict[str, object]],
    *,
    chunk_size: int = 100,
) -> dict[str, object]:
    chunk_names: list[str] = []
    chunk_counts: list[int] = []
    upto_names: list[str] = []
    running_count = 0
    for chunk_idx, start in enumerate(range(0, len(records), chunk_size)):
        chunk_name = f"{name}Chunk{chunk_idx:03d}"
        chunk_records = records[start:start + chunk_size]
        chunk_names.append(chunk_name)
        chunk_counts.append(len(chunk_records))
        emit_periodic_main_pair_finset_def(chunk_name, chunk_records)
        print(f"theorem {chunk_name}_card :")
        print(f"    {chunk_name}.card = {len(chunk_records)} := by")
        print("  native_decide")
        print()
        emit_periodic_main_chunk_subset_full_proof(
            chunk_name=chunk_name,
            chunk_records=chunk_records,
        )

    for idx, (chunk_name, chunk_count) in enumerate(zip(chunk_names, chunk_counts)):
        upto_name = f"{name}UpTo{idx:03d}"
        upto_names.append(upto_name)
        if idx == 0:
            running_count = chunk_count
            print(f"def {upto_name} : Finset (ℕ × ℕ) := {chunk_name}")
            print()
            print(f"theorem {upto_name}_card :")
            print(f"    {upto_name}.card = {running_count} := by")
            print(f"  simpa [{upto_name}] using {chunk_name}_card")
            print()
            print(f"theorem {upto_name}_subset_fullBlockSquarefreeExplicit :")
            print(f"    {upto_name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
            print(f"  simpa [{upto_name}] using {chunk_name}_subset_fullBlockSquarefreeExplicit")
            print()
        else:
            prev_name = upto_names[idx - 1]
            prev_count = running_count
            running_count += chunk_count
            print(f"def {upto_name} : Finset (ℕ × ℕ) :=")
            print(f"  {prev_name} ∪ {chunk_name}")
            print()
            print(f"theorem {prev_name}_disjoint_{chunk_name} :")
            print(f"    Disjoint {prev_name} {chunk_name} := by")
            print("  native_decide")
            print()
            print(f"theorem {upto_name}_card :")
            print(f"    {upto_name}.card = {running_count} := by")
            print(f"  rw [{upto_name}, Finset.card_union_of_disjoint {prev_name}_disjoint_{chunk_name}]")
            print(f"  norm_num [{prev_name}_card, {chunk_name}_card]")
            print()
            print(f"theorem {upto_name}_subset_fullBlockSquarefreeExplicit :")
            print(f"    {upto_name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
            print("  intro p hp")
            print(f"  rw [{upto_name}] at hp")
            print("  rcases Finset.mem_union.mp hp with hp | hp")
            print(f"  · exact {prev_name}_subset_fullBlockSquarefreeExplicit hp")
            print(f"  · exact {chunk_name}_subset_fullBlockSquarefreeExplicit hp")
            print()

    final_upto_name = upto_names[-1]
    print(f"def {name} : Finset (ℕ × ℕ) := {final_upto_name}")
    print()
    print(f"theorem {name}_card :")
    print(f"    {name}.card = {len(records)} := by")
    print(f"  simpa [{name}] using {final_upto_name}_card")
    print()
    print(f"theorem {name}_subset_fullBlockSquarefreeExplicit :")
    print(f"    {name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
    print(f"  simpa [{name}] using {final_upto_name}_subset_fullBlockSquarefreeExplicit")
    print()
    return {
        "chunk_names": chunk_names,
        "upto_names": upto_names,
        "final_upto_name": final_upto_name,
        "count": len(records),
    }


def emit_periodic_main_disjoint_from_chunks(
    *,
    left_name: str,
    right_name: str,
    right_chunks: list[str],
    right_upto: list[str],
) -> None:
    for idx, chunk_name in enumerate(right_chunks):
        print(f"theorem {left_name}_disjoint_{chunk_name} :")
        print(f"    Disjoint {left_name} {chunk_name} := by")
        print("  native_decide")
        print()
        upto_name = right_upto[idx]
        if idx == 0:
            print(f"theorem {left_name}_disjoint_{upto_name} :")
            print(f"    Disjoint {left_name} {upto_name} := by")
            print(f"  simpa [{upto_name}] using {left_name}_disjoint_{chunk_name}")
            print()
        else:
            prev_upto = right_upto[idx - 1]
            print(f"theorem {left_name}_disjoint_{upto_name} :")
            print(f"    Disjoint {left_name} {upto_name} := by")
            print(f"  rw [{upto_name}]")
            print("  exact Finset.disjoint_union_right.mpr")
            print(f"    ⟨{left_name}_disjoint_{prev_upto}, {left_name}_disjoint_{chunk_name}⟩")
            print()
    print(f"theorem {left_name}_disjoint_{right_name} :")
    print(f"    Disjoint {left_name} {right_name} := by")
    print(f"  simpa [{right_name}] using {left_name}_disjoint_{right_upto[-1]}")
    print()


def emit_periodic_main_coverage_lean(
    *,
    nonzero_records: list[dict[str, object]],
    zero_records: list[dict[str, object]],
) -> None:
    full_count = len(nonzero_records) + len(zero_records)
    emit_periodic_main_pair_primitive_lean_header()
    print("/- Generated periodic-main ordered-record coverage facts. -/")
    print()
    nonzero_info = emit_periodic_main_record_set_certificate(
        "PeriodicMainNonzeroRecordPairs", nonzero_records
    )
    zero_info = emit_periodic_main_record_set_certificate(
        "PeriodicMainZeroRecordPairs", zero_records
    )
    emit_periodic_main_disjoint_from_chunks(
        left_name="PeriodicMainNonzeroRecordPairs",
        right_name="PeriodicMainZeroRecordPairs",
        right_chunks=list(zero_info["chunk_names"]),
        right_upto=list(zero_info["upto_names"]),
    )
    print("def PeriodicMainAllRecordPairs : Finset (ℕ × ℕ) :=")
    print("  PeriodicMainNonzeroRecordPairs ∪ PeriodicMainZeroRecordPairs")
    print()
    print("theorem PeriodicMainAllRecordPairs_card :")
    print(f"    PeriodicMainAllRecordPairs.card = {full_count} := by")
    print("  rw [PeriodicMainAllRecordPairs,")
    print("    Finset.card_union_of_disjoint")
    print("      PeriodicMainNonzeroRecordPairs_disjoint_PeriodicMainZeroRecordPairs]")
    print("  norm_num [PeriodicMainNonzeroRecordPairs_card, PeriodicMainZeroRecordPairs_card]")
    print()
    print("theorem PeriodicMainFullBlockSquarefreeExplicit_card :")
    print(f"    PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit.card = {full_count} := by")
    print("  native_decide")
    print()
    print("theorem PeriodicMainAllRecordPairs_subset_fullBlockSquarefreeExplicit :")
    print("    PeriodicMainAllRecordPairs ⊆")
    print("      PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
    print("  intro p hp")
    print("  rw [PeriodicMainAllRecordPairs] at hp")
    print("  rcases Finset.mem_union.mp hp with hp | hp")
    print("  · exact PeriodicMainNonzeroRecordPairs_subset_fullBlockSquarefreeExplicit hp")
    print("  · exact PeriodicMainZeroRecordPairs_subset_fullBlockSquarefreeExplicit hp")
    print()
    print("theorem PeriodicMainAllRecordPairs_eq_fullBlockSquarefreeExplicit :")
    print("    PeriodicMainAllRecordPairs =")
    print("      PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
    print("  apply Finset.eq_of_subset_of_card_le")
    print("    PeriodicMainAllRecordPairs_subset_fullBlockSquarefreeExplicit")
    print("  rw [PeriodicMainAllRecordPairs_card, PeriodicMainFullBlockSquarefreeExplicit_card]")
    print()
    print("theorem PeriodicMainAllRecordPairs_eq_fullBlockExplicit :")
    print("    PeriodicMainAllRecordPairs =")
    print("      PeriodicMainFullBlockOrderedPairSupportExplicit := by")
    print("  rw [PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]")
    print("  exact PeriodicMainAllRecordPairs_eq_fullBlockSquarefreeExplicit")
    print()
    print("theorem PeriodicMainFullBlockExplicit_subset_allRecordPairs :")
    print("    PeriodicMainFullBlockOrderedPairSupportExplicit ⊆ PeriodicMainAllRecordPairs := by")
    print("  intro p hp")
    print("  rw [PeriodicMainAllRecordPairs_eq_fullBlockExplicit]")
    print("  exact hp")
    print()
    print("theorem PeriodicMainAllRecordPairs_subset_fullBlockExplicit :")
    print("    PeriodicMainAllRecordPairs ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by")
    print("  intro p hp")
    print("  rw [PeriodicMainAllRecordPairs_eq_fullBlockExplicit] at hp")
    print("  exact hp")
    print()
    print("theorem PeriodicMainNonzeroRecordPairs_disjoint_zeroRecordPairs :")
    print("    Disjoint PeriodicMainNonzeroRecordPairs PeriodicMainZeroRecordPairs := by")
    print("  exact PeriodicMainNonzeroRecordPairs_disjoint_PeriodicMainZeroRecordPairs")
    print()
    print("theorem PeriodicMainFullBlockExplicit_not_nonzero_mem_zero")
    print("    {p : ℕ × ℕ}")
    print("    (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit)")
    print("    (hnot : p ∉ PeriodicMainNonzeroRecordPairs) :")
    print("    p ∈ PeriodicMainZeroRecordPairs := by")
    print("  have hpAll : p ∈ PeriodicMainAllRecordPairs := PeriodicMainFullBlockExplicit_subset_allRecordPairs hp")
    print("  unfold PeriodicMainAllRecordPairs at hpAll")
    print("  exact (Finset.mem_union.mp hpAll).resolve_left hnot")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def load_periodic_main_ordered_record_payload(path: str, *, expected_mode: str | None = None) -> dict[str, object]:
    with open(path, "r", encoding="utf-8") as fh:
        payload = json.load(fh)
    mode = payload.get("mode")
    allowed_modes = {
        "periodic-main-ordered-nonzero-records",
        "periodic-main-ordered-zero-records",
    }
    if expected_mode is not None:
        if mode != expected_mode:
            raise SystemExit(f"{path}: expected {expected_mode}, found {mode}")
    elif mode not in allowed_modes:
        raise SystemExit(f"{path}: not a periodic-main ordered-record payload")
    return payload


def periodic_main_ordered_records_to_values(
    records: list[dict[str, object]],
) -> dict[tuple[int, int], Fraction]:
    values: dict[tuple[int, int], Fraction] = {}
    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        key = (q, q2)
        if key in values:
            raise SystemExit(f"duplicate periodic-main ordered record for {key}")
        values[key] = Fraction(int(record["value_num"]), int(record["value_den"]))
    return values


def make_periodic_main_row_slices(
    *,
    ordered_pairs: set[tuple[int, int]],
    row_batch_size: int,
    row_plan: str,
    target_pairs: int,
    single_threshold: int,
    max_width: int,
) -> list[tuple[int, int]]:
    if row_plan == "fixed":
        if row_batch_size <= 0:
            raise SystemExit("--periodic-main-row-batch-size must be positive")
        return [(lo, min(5001, lo + row_batch_size)) for lo in range(1, 5001, row_batch_size)]

    if row_plan != "density":
        raise SystemExit(f"unknown periodic-main row plan: {row_plan}")
    if target_pairs <= 0:
        raise SystemExit("--periodic-main-row-target-pairs must be positive")
    if single_threshold <= 0:
        raise SystemExit("--periodic-main-row-single-threshold must be positive")
    if max_width <= 0:
        raise SystemExit("--periodic-main-row-max-width must be positive")

    row_counts: dict[int, int] = defaultdict(int)
    for q, _q2 in ordered_pairs:
        row_counts[q] += 1

    rows: list[tuple[int, int]] = []
    lo = 1
    while lo <= 5000:
        if row_counts.get(lo, 0) >= single_threshold:
            rows.append((lo, lo + 1))
            lo += 1
            continue
        hi = lo
        running = 0
        while hi <= 5000:
            count = row_counts.get(hi, 0)
            if hi > lo and count >= single_threshold:
                break
            if hi > lo and (running + count > target_pairs or hi - lo >= max_width):
                break
            running += count
            hi += 1
            if running >= target_pairs or hi - lo >= max_width:
                break
        if hi == lo:
            hi = lo + 1
        rows.append((lo, hi))
        lo = hi
    return rows


def emit_periodic_main_row_exact_json(
    *,
    X: int,
    row: int,
    active_support: list[int],
    mu: list[int],
    phi: list[int],
    spf: list[int],
    even_window_card: int,
    out_path: str,
    progress: bool = False,
    progress_every: int = 100,
) -> None:
    if row <= 0:
        raise SystemExit("--emit-periodic-main-row-exact-json expects a positive row")
    if row not in active_support:
        raise SystemExit(f"row {row} is not in the active periodic-main support")

    row_pairs = [
        (row, q2)
        for q2 in active_support
        if q2 != row and 2 * math.lcm(row, q2) <= H + 1
    ]
    q_needed = sorted({row} | {q2 for _q, q2 in row_pairs})
    exact_ctx = build_surrogate_boundary_exact_context(
        X,
        mu,
        phi,
        spf,
        even_window_card,
        q_needed,
        progress=progress,
        progress_every_q=max(1, progress_every),
    )

    records: list[dict[str, object]] = []
    total = Fraction(0, 1)
    nonzero_count = 0
    started = time.time()
    for idx, (q, q2) in enumerate(row_pairs, start=1):
        value = centered_ramanujan_pair_periodic_main_term_rat_cached(X, q, q2, exact_ctx)
        if value != 0:
            nonzero_count += 1
        total += value
        records.append({
            "q": q,
            "q2": q2,
            "value_num": value.numerator,
            "value_den": value.denominator,
        })
        if progress and (idx % max(1, progress_every) == 0 or idx == len(row_pairs)):
            elapsed = time.time() - started
            print(
                f"[periodic-main-row-exact-json] row={row} "
                f"processed={idx}/{len(row_pairs)} elapsed={elapsed:.1f}s",
                file=sys.stderr,
                flush=True,
            )

    payload = {
        "mode": "periodic-main-ordered-nonzero-records",
        "submode": "periodic-main-row-exact-all-records",
        "X": X,
        "row": row,
        "active_support_card": len(active_support),
        "row_record_count": len(records),
        "row_nonzero_record_count": nonzero_count,
        "row_zero_record_count": len(records) - nonzero_count,
        "total_num": total.numerator,
        "total_den": total.denominator,
        "records": records,
    }
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, sort_keys=True)
    print("Periodic-main row exact JSON report")
    print(f"  X               = {X}")
    print(f"  row             = {row}")
    print(f"  records         = {len(records)}")
    print(f"  nonzero records = {nonzero_count}")
    print(f"  zero records    = {len(records) - nonzero_count}")
    print(f"  total           = {fraction_to_q_literal(total)}")
    print(f"  wrote           = {out_path}")


def emit_periodic_main_row_batch_assembly_lean(
    *,
    nonzero_records: list[dict[str, object]],
    zero_records: list[dict[str, object]],
    row_batch_size: int,
    row_plan: str,
    target_pairs: int,
    single_threshold: int,
    max_width: int,
) -> None:
    values = periodic_main_ordered_records_to_values(nonzero_records)
    zero_values = periodic_main_ordered_records_to_values(zero_records)
    overlap = set(values).intersection(zero_values)
    if overlap:
        sample = sorted(overlap)[:5]
        raise SystemExit(f"nonzero and zero periodic-main records overlap: {sample}")
    values.update(zero_values)

    row_slices = make_periodic_main_row_slices(
        ordered_pairs=set(values),
        row_batch_size=row_batch_size,
        row_plan=row_plan,
        target_pairs=target_pairs,
        single_threshold=single_threshold,
        max_width=max_width,
    )

    rows: list[tuple[int, int, Fraction]] = []
    for lo, hi in row_slices:
        total = Fraction(0, 1)
        for (q, _q2), value in values.items():
            if lo <= q < hi:
                total += value
        rows.append((lo, hi, total))

    grand_total = sum((row_total for _lo, _hi, row_total in rows), Fraction(0, 1))

    emit_periodic_main_pair_primitive_lean_header()
    print("/- Generated row-batch assembly surface for the periodic-main exact payload. -/")
    print()
    for idx, (lo, hi, total) in enumerate(rows):
        print(f"def PeriodicMainRowSliceTotal{idx:03d} : ℚ :=")
        print(f"  {fraction_to_q_literal(total)}")
        print(f"-- rows [{lo}, {hi})")
        print()

    print("structure PeriodicMainRowSliceSumCertificateAtX0 : Prop where")
    for idx, (lo, hi, _total) in enumerate(rows):
        print(f"  h{idx:03d} :")
        print(
            f"    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit {lo} {hi},"
        )
        print("      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)")
        print(f"      = PeriodicMainRowSliceTotal{idx:03d}")
    print()

    print("theorem periodicMainCert_true_of_rowSliceSums")
    for idx, (lo, hi, _total) in enumerate(rows):
        print(f"    (h{idx:03d} :")
        print(
            f"      (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit {lo} {hi},"
        )
        print("        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)")
        print(f"        = PeriodicMainRowSliceTotal{idx:03d})")
    print("    :")
    print("    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0 =")
    print("      surrogatePeriodicMainX0RatCert := by")
    print("  apply surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_cert_of_squarefreeFullBlockSum")
    print("  rw [← PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainder_one]")
    for lo, hi, _total in rows:
        print(
            "  rw [PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainder_sum_split "
            f"{lo} {hi} (by norm_num) (surrogatePeriodicMainActiveOrderedPairSummandRat X0)]"
        )
    print("  rw [PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainder_5001_eq_empty]")
    print("  simp only [Finset.sum_empty, add_zero]")
    for idx in range(len(rows)):
        print(f"  rw [h{idx:03d}]")
    row_total_names = ", ".join(f"PeriodicMainRowSliceTotal{idx:03d}" for idx in range(len(rows)))
    print(f"  norm_num [surrogatePeriodicMainX0RatCert, {row_total_names}]")
    print()
    print("theorem periodicMainCert_true_of_rowSliceCertificate")
    print("    (cert : PeriodicMainRowSliceSumCertificateAtX0) :")
    print("    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0 =")
    print("      surrogatePeriodicMainX0RatCert := by")
    print("  exact periodicMainCert_true_of_rowSliceSums")
    for idx in range(len(rows)):
        print(f"    cert.h{idx:03d}")
    print()
    print("theorem periodicMainRowBatchTotals_sum_check :")
    print("    (")
    for idx in range(len(rows)):
        sep = " +" if idx + 1 < len(rows) else ""
        print(f"      PeriodicMainRowSliceTotal{idx:03d}{sep}")
    print(f"    ) = {fraction_to_q_literal(grand_total)} := by")
    print(f"  norm_num [{row_total_names}]")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_record_set_coverage_lean(
    *,
    name: str,
    records: list[dict[str, object]],
) -> None:
    emit_periodic_main_pair_primitive_lean_header()
    print(f"/- Generated periodic-main ordered-record coverage facts for {name}. -/")
    print()
    emit_periodic_main_record_set_certificate(name, records)
    emit_periodic_main_pair_primitive_lean_footer()


def periodic_main_row_record_complexity_report(
    *,
    payload_path: str,
    top: int,
    group_size: int,
    completed_records: int,
    json_out: str = "",
) -> None:
    if group_size <= 0:
        raise SystemExit("--periodic-main-row-record-complexity-group-size must be positive")
    if top <= 0:
        raise SystemExit("--periodic-main-row-record-complexity-top must be positive")

    with open(payload_path, "r", encoding="utf-8") as fh:
        payload = json.load(fh)
    if payload.get("submode") != "periodic-main-row-exact-all-records":
        raise SystemExit(f"{payload_path}: not a periodic-main row exact-record payload")

    records = list(payload.get("records", []))
    row = int(payload.get("row", 0))
    spf = spf_sieve(Q0)
    record_rows: list[dict[str, object]] = []
    group_rows: dict[int, dict[str, object]] = {}

    for idx, record in enumerate(records):
        q = int(record["q"])
        q2 = int(record["q2"])
        value_num = int(record["value_num"])
        value_den = int(record["value_den"])
        divs_q = divisors_from_factorization(factorization(q, spf))
        divs_q2 = divisors_from_factorization(factorization(q2, spf))
        left_count = len(divs_q)
        right_count = len(divs_q2)
        term_atoms = left_count * right_count
        period = block_period(q, q2)
        full_blocks = (H + 1) // period
        joint_moduli = [math.lcm(q // g, q2 // h) for g in divs_q for h in divs_q2]
        divisor_lcms = [math.lcm(g, h) for g in divs_q for h in divs_q2]
        max_joint_modulus = max(joint_moduli) if joint_moduli else 0
        max_divisor_lcm = max(divisor_lcms) if divisor_lcms else 0
        current_fact_instances = 7 * term_atoms
        cached_fact_instances = 3 * left_count + 3 * right_count + term_atoms
        fact_reuse_savings = current_fact_instances - cached_fact_instances
        value_abs = Fraction(abs(value_num), value_den)
        row_data = {
            "index": idx,
            "q": q,
            "q2": q2,
            "zero": value_num == 0,
            "value_num": str(value_num),
            "value_den": str(value_den),
            "left_divisors": left_count,
            "right_divisors": right_count,
            "term_atoms": term_atoms,
            "block_period": period,
            "full_blocks": full_blocks,
            "max_joint_modulus": max_joint_modulus,
            "max_divisor_lcm": max_divisor_lcm,
            "current_fact_instances_est": current_fact_instances,
            "cached_fact_instances_est": cached_fact_instances,
            "fact_reuse_savings_est": fact_reuse_savings,
            "value_abs_num": str(value_abs.numerator),
            "value_abs_den": str(value_abs.denominator),
        }
        record_rows.append(row_data)

        group_index = idx // group_size
        group = group_rows.setdefault(
            group_index,
            {
                "group": group_index,
                "start": group_index * group_size,
                "end": min(len(records), (group_index + 1) * group_size),
                "records": 0,
                "zero_records": 0,
                "nonzero_records": 0,
                "term_atoms": 0,
                "max_term_atoms": 0,
                "max_joint_modulus": 0,
                "fact_reuse_savings_est": 0,
                "abs_value": Fraction(0),
                "signed_value": Fraction(0),
            },
        )
        group["records"] = int(group["records"]) + 1
        if value_num == 0:
            group["zero_records"] = int(group["zero_records"]) + 1
        else:
            group["nonzero_records"] = int(group["nonzero_records"]) + 1
        group["term_atoms"] = int(group["term_atoms"]) + term_atoms
        group["max_term_atoms"] = max(int(group["max_term_atoms"]), term_atoms)
        group["max_joint_modulus"] = max(int(group["max_joint_modulus"]), max_joint_modulus)
        group["fact_reuse_savings_est"] = int(group["fact_reuse_savings_est"]) + fact_reuse_savings
        group["abs_value"] = group["abs_value"] + value_abs
        group["signed_value"] = group["signed_value"] + Fraction(value_num, value_den)

    def fraction_decimal(fr: Fraction, places: int = 12) -> str:
        sign = "-" if fr < 0 else ""
        fr_abs = abs(fr)
        scale = 10 ** places
        scaled = fr_abs.numerator * scale // fr_abs.denominator
        whole, frac = divmod(scaled, scale)
        return f"{sign}{whole}.{frac:0{places}d}"

    group_list: list[dict[str, object]] = []
    for group in sorted(group_rows.values(), key=lambda item: int(item["group"])):
        abs_value = group.pop("abs_value")
        signed_value = group.pop("signed_value")
        assert isinstance(abs_value, Fraction)
        assert isinstance(signed_value, Fraction)
        group["abs_value_num"] = str(abs_value.numerator)
        group["abs_value_den"] = str(abs_value.denominator)
        group["signed_value_num"] = str(signed_value.numerator)
        group["signed_value_den"] = str(signed_value.denominator)
        group["abs_value_decimal"] = fraction_decimal(abs_value, 8)
        group["signed_value_decimal"] = fraction_decimal(signed_value, 8)
        group_list.append(group)

    completed_records = max(0, min(completed_records, len(records)))
    completed_groups = completed_records // group_size
    total_terms = sum(int(row_data["term_atoms"]) for row_data in record_rows)
    total_fact_savings = sum(int(row_data["fact_reuse_savings_est"]) for row_data in record_rows)
    pending_terms = sum(
        int(row_data["term_atoms"]) for row_data in record_rows[completed_records:]
    )
    pending_fact_savings = sum(
        int(row_data["fact_reuse_savings_est"]) for row_data in record_rows[completed_records:]
    )

    print("[summary]")
    print(f"payload: {payload_path}")
    print(f"row: {row}")
    print(f"records: {len(records)}")
    print(f"nonzero records: {payload.get('row_nonzero_record_count')}")
    print(f"zero records: {payload.get('row_zero_record_count')}")
    print(f"group size: {group_size}")
    print(f"completed records checkpoint: {completed_records}")
    print(f"completed full groups checkpoint: {completed_groups}")
    print(f"remaining records: {len(records) - completed_records}")
    print(f"total term atoms: {total_terms}")
    print(f"remaining term atoms: {pending_terms}")
    print(f"estimated reusable fact savings, all: {total_fact_savings}")
    print(f"estimated reusable fact savings, remaining: {pending_fact_savings}")
    print()

    def print_record_table(title: str, rows: list[dict[str, object]]) -> None:
        print(title)
        print("idx\tq\tq2\tzero\tldiv\trdiv\tterms\tperiod\tblocks\tmaxJoint\tfactSavings")
        for row_data in rows[:top]:
            print(
                f"{row_data['index']}\t{row_data['q']}\t{row_data['q2']}\t{row_data['zero']}\t"
                f"{row_data['left_divisors']}\t{row_data['right_divisors']}\t"
                f"{row_data['term_atoms']}\t{row_data['block_period']}\t{row_data['full_blocks']}\t"
                f"{row_data['max_joint_modulus']}\t{row_data['fact_reuse_savings_est']}"
            )
        print()

    print_record_table(
        "[top records by term atoms]",
        sorted(record_rows, key=lambda item: (-int(item["term_atoms"]), int(item["index"]))),
    )
    print_record_table(
        "[top records by max joint modulus]",
        sorted(record_rows, key=lambda item: (-int(item["max_joint_modulus"]), int(item["index"]))),
    )
    print_record_table(
        "[top pending records by estimated cached-fact savings]",
        sorted(
            record_rows[completed_records:],
            key=lambda item: (-int(item["fact_reuse_savings_est"]), int(item["index"])),
        ),
    )

    print("[top groups by remaining term atoms]")
    print("group\trange\trecords\tzero\tnonzero\tterms\tmaxTerms\tmaxJoint\tfactSavings\tsigned\tabs")
    pending_groups = [group for group in group_list if int(group["end"]) > completed_records]
    for group in sorted(pending_groups, key=lambda item: (-int(item["term_atoms"]), int(item["group"])))[:top]:
        print(
            f"{group['group']}\t[{group['start']},{group['end']})\t{group['records']}\t"
            f"{group['zero_records']}\t{group['nonzero_records']}\t{group['term_atoms']}\t"
            f"{group['max_term_atoms']}\t{group['max_joint_modulus']}\t"
            f"{group['fact_reuse_savings_est']}\t{group['signed_value_decimal']}\t"
            f"{group['abs_value_decimal']}"
        )
    print()

    report_json = {
        "payload": payload_path,
        "row": row,
        "record_count": len(records),
        "group_size": group_size,
        "completed_records": completed_records,
        "completed_groups": completed_groups,
        "total_term_atoms": total_terms,
        "remaining_term_atoms": pending_terms,
        "total_fact_reuse_savings_est": total_fact_savings,
        "remaining_fact_reuse_savings_est": pending_fact_savings,
        "records": record_rows,
        "groups": group_list,
    }
    if json_out:
        with open(json_out, "w", encoding="utf-8") as fh:
            json.dump(report_json, fh, indent=2, sort_keys=True)
            fh.write("\n")
        print(f"[write] {json_out}", file=sys.stderr)


def emit_periodic_main_record_set_coverage_chunk_lean(
    *,
    name: str,
    records: list[dict[str, object]],
    chunk_idx: int,
    chunk_size: int = 100,
) -> None:
    start = chunk_idx * chunk_size
    end = min(len(records), start + chunk_size)
    if start >= len(records):
        raise SystemExit(f"chunk index {chunk_idx} out of range for {len(records)} records")
    chunk_name = f"{name}Chunk{chunk_idx:03d}"
    chunk_records = records[start:end]
    emit_periodic_main_pair_primitive_lean_header()
    print(
        f"/- Generated periodic-main ordered-record coverage facts for "
        f"{chunk_name}, JSON indices [{start},{end}). -/"
    )
    print()
    emit_periodic_main_pair_finset_def(chunk_name, chunk_records)
    print(f"theorem {chunk_name}_card :")
    print(f"    {chunk_name}.card = {len(chunk_records)} := by")
    print("  native_decide")
    print()
    emit_periodic_main_chunk_subset_full_proof(
        chunk_name=chunk_name,
        chunk_records=chunk_records,
    )
    emit_periodic_main_pair_primitive_lean_footer()


def periodic_main_record_chunk_count(records: list[dict[str, object]], chunk_size: int) -> int:
    return (len(records) + chunk_size - 1) // chunk_size


def emit_periodic_main_record_set_coverage_chunk_files(
    *,
    records: list[dict[str, object]],
    name: str,
    out_dir: str,
    file_prefix: str,
    chunk_size: int = 100,
    skip_existing: bool = False,
) -> None:
    os.makedirs(out_dir, exist_ok=True)
    chunk_count = periodic_main_record_chunk_count(records, chunk_size)
    for chunk_idx in range(chunk_count):
        path = os.path.join(out_dir, f"{file_prefix}{chunk_idx:03d}.lean")
        if skip_existing and os.path.exists(path):
            print(f"[periodic-main coverage chunks] skip existing {path}", file=sys.stderr)
            continue
        with open(path, "w", encoding="utf-8") as out:
            old_stdout = sys.stdout
            try:
                sys.stdout = out
                emit_periodic_main_record_set_coverage_chunk_lean(
                    name=name,
                    records=records,
                    chunk_idx=chunk_idx,
                    chunk_size=chunk_size,
                )
            finally:
                sys.stdout = old_stdout
        print(
            f"[periodic-main coverage chunks] wrote {path} "
            f"({chunk_idx + 1}/{chunk_count})",
            file=sys.stderr,
        )


def emit_periodic_main_record_set_union_assembly_lean(
    *,
    name: str,
    part_names: list[str],
    part_counts: list[int],
    imports: list[str],
) -> None:
    if len(part_names) != len(part_counts):
        raise ValueError("part_names and part_counts length mismatch")
    upto_names = [f"{name}UpTo{idx:03d}" for idx in range(len(part_names))]
    emit_periodic_main_pair_primitive_lean_header(imports)
    print(f"/- Generated periodic-main ordered-record union assembly facts for {name}. -/")
    print()
    running_count = 0
    for idx, (part_name, part_count) in enumerate(zip(part_names, part_counts)):
        upto_name = upto_names[idx]
        if idx == 0:
            running_count = part_count
            print(f"def {upto_name} : Finset (ℕ × ℕ) := {part_name}")
            print()
            print(f"theorem {upto_name}_card :")
            print(f"    {upto_name}.card = {running_count} := by")
            print(f"  simpa [{upto_name}] using {part_name}_card")
            print()
            print(f"theorem {upto_name}_subset_fullBlockSquarefreeExplicit :")
            print(f"    {upto_name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
            print(f"  simpa [{upto_name}] using {part_name}_subset_fullBlockSquarefreeExplicit")
            print()
        else:
            prev_name = upto_names[idx - 1]
            running_count += part_count
            print(f"def {upto_name} : Finset (ℕ × ℕ) :=")
            print(f"  {prev_name} ∪ {part_name}")
            print()
            print(f"theorem {prev_name}_disjoint_{part_name} :")
            print(f"    Disjoint {prev_name} {part_name} := by")
            print("  native_decide")
            print()
            print(f"theorem {upto_name}_card :")
            print(f"    {upto_name}.card = {running_count} := by")
            print(f"  rw [{upto_name}, Finset.card_union_of_disjoint {prev_name}_disjoint_{part_name}]")
            print(f"  norm_num [{prev_name}_card, {part_name}_card]")
            print()
            print(f"theorem {upto_name}_subset_fullBlockSquarefreeExplicit :")
            print(f"    {upto_name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
            print("  intro p hp")
            print(f"  rw [{upto_name}] at hp")
            print("  rcases Finset.mem_union.mp hp with hp | hp")
            print(f"  · exact {prev_name}_subset_fullBlockSquarefreeExplicit hp")
            print(f"  · exact {part_name}_subset_fullBlockSquarefreeExplicit hp")
            print()

    record_count = sum(part_counts)
    if not upto_names:
        print(f"def {name} : Finset (ℕ × ℕ) := ∅")
        print()
    else:
        print(f"def {name} : Finset (ℕ × ℕ) := {upto_names[-1]}")
        print()
    print(f"theorem {name}_card :")
    print(f"    {name}.card = {record_count} := by")
    if not upto_names:
        print("  native_decide")
    else:
        print(f"  simpa [{name}] using {upto_names[-1]}_card")
    print()
    print(f"theorem {name}_subset_fullBlockSquarefreeExplicit :")
    print(f"    {name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
    if not upto_names:
        print("  intro p hp")
        print(f"  simp [{name}] at hp")
    else:
        print(f"  simpa [{name}] using {upto_names[-1]}_subset_fullBlockSquarefreeExplicit")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_record_set_union_light_assembly_lean(
    *,
    name: str,
    part_names: list[str],
    part_counts: list[int],
    imports: list[str],
) -> None:
    """Assemble already-large imported parts without pairwise disjoint proofs.

    The chunk-to-group files prove cardinalities via small disjointness checks.
    At the final grouped layer, accumulated disjointness can be more expensive
    than directly evaluating the cardinality of the small union of imported
    groups.  This keeps the final wrapper shallow while retaining imported
    subset facts.
    """
    if len(part_names) != len(part_counts):
        raise ValueError("part_names and part_counts length mismatch")
    upto_names = [f"{name}UpTo{idx:03d}" for idx in range(len(part_names))]
    emit_periodic_main_pair_primitive_lean_header(imports)
    print(f"/- Generated periodic-main ordered-record light union assembly facts for {name}. -/")
    print()
    for idx, part_name in enumerate(part_names):
        upto_name = upto_names[idx]
        if idx == 0:
            print(f"def {upto_name} : Finset (ℕ × ℕ) := {part_name}")
            print()
            print(f"theorem {upto_name}_subset_fullBlockSquarefreeExplicit :")
            print(f"    {upto_name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
            print(f"  simpa [{upto_name}] using {part_name}_subset_fullBlockSquarefreeExplicit")
            print()
        else:
            prev_name = upto_names[idx - 1]
            print(f"def {upto_name} : Finset (ℕ × ℕ) :=")
            print(f"  {prev_name} ∪ {part_name}")
            print()
            print(f"theorem {upto_name}_subset_fullBlockSquarefreeExplicit :")
            print(f"    {upto_name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
            print("  intro p hp")
            print(f"  rw [{upto_name}] at hp")
            print("  rcases Finset.mem_union.mp hp with hp | hp")
            print(f"  · exact {prev_name}_subset_fullBlockSquarefreeExplicit hp")
            print(f"  · exact {part_name}_subset_fullBlockSquarefreeExplicit hp")
            print()

    record_count = sum(part_counts)
    if not upto_names:
        print(f"def {name} : Finset (ℕ × ℕ) := ∅")
        print()
    else:
        print(f"def {name} : Finset (ℕ × ℕ) := {upto_names[-1]}")
        print()
    print(f"theorem {name}_card :")
    print(f"    {name}.card = {record_count} := by")
    print("  native_decide")
    print()
    print(f"theorem {name}_subset_fullBlockSquarefreeExplicit :")
    print(f"    {name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
    if not upto_names:
        print("  intro p hp")
        print(f"  simp [{name}] at hp")
    else:
        print(f"  simpa [{name}] using {upto_names[-1]}_subset_fullBlockSquarefreeExplicit")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_record_set_coverage_group_files(
    *,
    records: list[dict[str, object]],
    name: str,
    out_dir: str,
    file_prefix: str,
    chunk_module_prefix: str,
    chunk_size: int = 100,
    group_chunk_size: int = 25,
    skip_existing: bool = False,
) -> None:
    os.makedirs(out_dir, exist_ok=True)
    chunk_count = periodic_main_record_chunk_count(records, chunk_size)
    chunk_counts = [
        min(chunk_size, len(records) - idx * chunk_size)
        for idx in range(chunk_count)
    ]
    group_count = (chunk_count + group_chunk_size - 1) // group_chunk_size
    for group_idx in range(group_count):
        start = group_idx * group_chunk_size
        end = min(chunk_count, start + group_chunk_size)
        path = os.path.join(out_dir, f"{file_prefix}{group_idx:03d}.lean")
        if skip_existing and os.path.exists(path):
            print(f"[periodic-main coverage groups] skip existing {path}", file=sys.stderr)
            continue
        group_name = f"{name}Group{group_idx:03d}"
        part_names = [f"{name}Chunk{idx:03d}" for idx in range(start, end)]
        part_counts = chunk_counts[start:end]
        imports = [f"{chunk_module_prefix}{idx:03d}" for idx in range(start, end)]
        with open(path, "w", encoding="utf-8") as out:
            old_stdout = sys.stdout
            try:
                sys.stdout = out
                emit_periodic_main_record_set_union_assembly_lean(
                    name=group_name,
                    part_names=part_names,
                    part_counts=part_counts,
                    imports=imports,
                )
            finally:
                sys.stdout = old_stdout
        print(
            f"[periodic-main coverage groups] wrote {path} "
            f"({group_idx + 1}/{group_count})",
            file=sys.stderr,
        )


def emit_periodic_main_record_set_coverage_grouped_assembly_lean(
    *,
    records: list[dict[str, object]],
    name: str,
    group_module_prefix: str,
    chunk_size: int = 100,
    group_chunk_size: int = 25,
) -> None:
    chunk_count = periodic_main_record_chunk_count(records, chunk_size)
    group_count = (chunk_count + group_chunk_size - 1) // group_chunk_size
    group_names = [f"{name}Group{idx:03d}" for idx in range(group_count)]
    group_counts: list[int] = []
    for group_idx in range(group_count):
        start_record = group_idx * group_chunk_size * chunk_size
        end_record = min(len(records), start_record + group_chunk_size * chunk_size)
        group_counts.append(end_record - start_record)
    imports = [f"{group_module_prefix}{idx:03d}" for idx in range(group_count)]
    emit_periodic_main_record_set_union_light_assembly_lean(
        name=name,
        part_names=group_names,
        part_counts=group_counts,
        imports=imports,
    )


def emit_periodic_main_record_set_coverage_chunk_assembly_lean(
    *,
    name: str,
    record_count: int,
    module_prefix: str,
    chunk_size: int = 100,
) -> None:
    chunk_count = (record_count + chunk_size - 1) // chunk_size
    chunk_names = [f"{name}Chunk{idx:03d}" for idx in range(chunk_count)]
    chunk_counts = [
        min(chunk_size, record_count - idx * chunk_size)
        for idx in range(chunk_count)
    ]
    upto_names = [f"{name}UpTo{idx:03d}" for idx in range(chunk_count)]
    imports = [f"{module_prefix}{idx:03d}" for idx in range(chunk_count)]
    emit_periodic_main_pair_primitive_lean_header(imports)
    print(f"/- Generated periodic-main ordered-record coverage assembly facts for {name}. -/")
    print()
    running_count = 0
    for idx, chunk_name in enumerate(chunk_names):
        upto_name = upto_names[idx]
        chunk_count_i = chunk_counts[idx]
        if idx == 0:
            running_count = chunk_count_i
            print(f"def {upto_name} : Finset (ℕ × ℕ) := {chunk_name}")
            print()
            print(f"theorem {upto_name}_card :")
            print(f"    {upto_name}.card = {running_count} := by")
            print(f"  simpa [{upto_name}] using {chunk_name}_card")
            print()
            print(f"theorem {upto_name}_subset_fullBlockSquarefreeExplicit :")
            print(f"    {upto_name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
            print(f"  simpa [{upto_name}] using {chunk_name}_subset_fullBlockSquarefreeExplicit")
            print()
        else:
            prev_name = upto_names[idx - 1]
            running_count += chunk_count_i
            print(f"def {upto_name} : Finset (ℕ × ℕ) :=")
            print(f"  {prev_name} ∪ {chunk_name}")
            print()
            print(f"theorem {prev_name}_disjoint_{chunk_name} :")
            print(f"    Disjoint {prev_name} {chunk_name} := by")
            print("  native_decide")
            print()
            print(f"theorem {upto_name}_card :")
            print(f"    {upto_name}.card = {running_count} := by")
            print(f"  rw [{upto_name}, Finset.card_union_of_disjoint {prev_name}_disjoint_{chunk_name}]")
            print(f"  norm_num [{prev_name}_card, {chunk_name}_card]")
            print()
            print(f"theorem {upto_name}_subset_fullBlockSquarefreeExplicit :")
            print(f"    {upto_name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
            print("  intro p hp")
            print(f"  rw [{upto_name}] at hp")
            print("  rcases Finset.mem_union.mp hp with hp | hp")
            print(f"  · exact {prev_name}_subset_fullBlockSquarefreeExplicit hp")
            print(f"  · exact {chunk_name}_subset_fullBlockSquarefreeExplicit hp")
            print()
    if not upto_names:
        print(f"def {name} : Finset (ℕ × ℕ) := ∅")
        print()
    else:
        print(f"def {name} : Finset (ℕ × ℕ) := {upto_names[-1]}")
        print()
    print(f"theorem {name}_card :")
    print(f"    {name}.card = {record_count} := by")
    if not upto_names:
        print(f"  native_decide")
    else:
        print(f"  simpa [{name}] using {upto_names[-1]}_card")
    print()
    print(f"theorem {name}_subset_fullBlockSquarefreeExplicit :")
    print(f"    {name} ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
    if not upto_names:
        print("  intro p hp")
        print(f"  simp [{name}] at hp")
    else:
        print(f"  simpa [{name}] using {upto_names[-1]}_subset_fullBlockSquarefreeExplicit")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_coverage_assembly_lean(
    *,
    nonzero_count: int,
    zero_count: int,
) -> None:
    full_count = nonzero_count + zero_count
    emit_periodic_main_pair_primitive_lean_header([
        "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzero",
        "Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZero",
    ])
    print("/- Generated periodic-main ordered-record coverage assembly facts. -/")
    print()
    print("def PeriodicMainAllRecordPairs : Finset (ℕ × ℕ) :=")
    print("  PeriodicMainNonzeroRecordPairs ∪ PeriodicMainZeroRecordPairs")
    print()
    print("theorem PeriodicMainNonzeroRecordPairs_disjoint_PeriodicMainZeroRecordPairs :")
    print("    Disjoint PeriodicMainNonzeroRecordPairs PeriodicMainZeroRecordPairs := by")
    print("  native_decide")
    print()
    print("theorem PeriodicMainAllRecordPairs_card :")
    print(f"    PeriodicMainAllRecordPairs.card = {full_count} := by")
    print("  rw [PeriodicMainAllRecordPairs,")
    print("    Finset.card_union_of_disjoint")
    print("      PeriodicMainNonzeroRecordPairs_disjoint_PeriodicMainZeroRecordPairs]")
    print("  norm_num [PeriodicMainNonzeroRecordPairs_card, PeriodicMainZeroRecordPairs_card]")
    print()
    print("theorem PeriodicMainFullBlockSquarefreeExplicit_card :")
    print(f"    PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit.card = {full_count} := by")
    print("  native_decide")
    print()
    print("theorem PeriodicMainAllRecordPairs_subset_fullBlockSquarefreeExplicit :")
    print("    PeriodicMainAllRecordPairs ⊆")
    print("      PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
    print("  intro p hp")
    print("  rw [PeriodicMainAllRecordPairs] at hp")
    print("  rcases Finset.mem_union.mp hp with hp | hp")
    print("  · exact PeriodicMainNonzeroRecordPairs_subset_fullBlockSquarefreeExplicit hp")
    print("  · exact PeriodicMainZeroRecordPairs_subset_fullBlockSquarefreeExplicit hp")
    print()
    print("theorem PeriodicMainAllRecordPairs_eq_fullBlockSquarefreeExplicit :")
    print("    PeriodicMainAllRecordPairs =")
    print("      PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by")
    print("  apply Finset.eq_of_subset_of_card_le")
    print("    PeriodicMainAllRecordPairs_subset_fullBlockSquarefreeExplicit")
    print("  rw [PeriodicMainAllRecordPairs_card, PeriodicMainFullBlockSquarefreeExplicit_card]")
    print()
    print("theorem PeriodicMainAllRecordPairs_eq_fullBlockExplicit :")
    print("    PeriodicMainAllRecordPairs =")
    print("      PeriodicMainFullBlockOrderedPairSupportExplicit := by")
    print("  rw [PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]")
    print("  exact PeriodicMainAllRecordPairs_eq_fullBlockSquarefreeExplicit")
    print()
    print("theorem PeriodicMainFullBlockExplicit_subset_allRecordPairs :")
    print("    PeriodicMainFullBlockOrderedPairSupportExplicit ⊆ PeriodicMainAllRecordPairs := by")
    print("  intro p hp")
    print("  rw [PeriodicMainAllRecordPairs_eq_fullBlockExplicit]")
    print("  exact hp")
    print()
    print("theorem PeriodicMainAllRecordPairs_subset_fullBlockExplicit :")
    print("    PeriodicMainAllRecordPairs ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by")
    print("  intro p hp")
    print("  rw [PeriodicMainAllRecordPairs_eq_fullBlockExplicit] at hp")
    print("  exact hp")
    print()
    print("theorem PeriodicMainNonzeroRecordPairs_disjoint_zeroRecordPairs :")
    print("    Disjoint PeriodicMainNonzeroRecordPairs PeriodicMainZeroRecordPairs := by")
    print("  exact PeriodicMainNonzeroRecordPairs_disjoint_PeriodicMainZeroRecordPairs")
    print()
    print("theorem PeriodicMainFullBlockExplicit_not_nonzero_mem_zero")
    print("    {p : ℕ × ℕ}")
    print("    (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit)")
    print("    (hnot : p ∉ PeriodicMainNonzeroRecordPairs) :")
    print("    p ∈ PeriodicMainZeroRecordPairs := by")
    print("  have hpAll : p ∈ PeriodicMainAllRecordPairs := PeriodicMainFullBlockExplicit_subset_allRecordPairs hp")
    print("  unfold PeriodicMainAllRecordPairs at hpAll")
    print("  exact (Finset.mem_union.mp hpAll).resolve_left hnot")
    print()
    emit_periodic_main_pair_primitive_lean_footer()


def emit_periodic_main_pair_primitive_lean_theorems(
    *,
    X: int,
    q: int,
    q2: int,
    exact_ctx: dict[str, object],
    expected_summand: Fraction | None = None,
    force_top_level_helpers: bool = False,
) -> None:
    name = f"periodicMainPair_{q}_{q2}_X{X}"
    if expected_summand == Fraction(0, 1) and (q in {1, 2} or q2 in {1, 2}):
        print(f"theorem {name}_orderedSummand :")
        print(f"    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk {q} {q2}) = (0 : ℚ) := by")
        if q == 1:
            print(f"  exact surrogatePeriodicMainActiveOrderedPairSummandRat_one_left_zero X0 (Prod.mk {q} {q2}) rfl (by norm_num)")
        elif q == 2:
            print(f"  exact surrogatePeriodicMainActiveOrderedPairSummandRat_two_left_zero X0 (Prod.mk {q} {q2}) rfl (by norm_num)")
        elif q2 == 1:
            print(f"  exact surrogatePeriodicMainActiveOrderedPairSummandRat_one_right_zero X0 (Prod.mk {q} {q2}) rfl (by norm_num)")
        else:
            print(f"  exact surrogatePeriodicMainActiveOrderedPairSummandRat_two_right_zero X0 (Prod.mk {q} {q2}) rfl (by norm_num)")
        print()
        return
    divs_q = exact_ctx["divisors_by_q"][q]
    divs_q2 = exact_ctx["divisors_by_q"][q2]
    first_even, even_count = full_block_even_progression(X, block_period(q, q2))
    coeff_q = exact_ctx["coeff_rat"][q]
    coeff_q2 = exact_ctx["coeff_rat"][q2]
    summand_value = centered_ramanujan_pair_periodic_main_term_rat_cached(X, q, q2, exact_ctx)
    if expected_summand is not None and summand_value != expected_summand:
        raise SystemExit(
            f"record ({q},{q2}) value mismatch: generated {summand_value} "
            f"but JSON record has {expected_summand}"
        )
    if coeff_q == 0 or coeff_q2 == 0:
        centered_term = Fraction(0, 1)
    else:
        centered_term = summand_value / (coeff_q * coeff_q2)

    def emit_block_periodic_count_proof(
        *,
        theorem_name: str,
        q0: int,
        g0: int,
        expected: int,
    ) -> None:
        print(
            f"  have {theorem_name} : "
            f"rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q0} {g0} = ({expected} : ℚ) := by"
        )
        print("    native_decide")

    def emit_pair_resolved_count_proof(
        *,
        theorem_name: str,
        g: int,
        h: int,
        expected: int,
    ) -> None:
        print(
            f"  have {theorem_name} : "
            f"rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} {g} {h} = ({expected} : ℚ) := by"
        )
        print("    native_decide")

    def term_expr_lines(g: int | str, h: int | str, *, indent: str = "      ") -> list[str]:
        return [
            f"{indent}ramanujanGcdClassCoeffRat {q} {g} * ramanujanGcdClassCoeffRat {q2} {h}",
            f"{indent}  * ((((H + 1) / centeredRamanujanPairBlockPeriod {q} {q2}) : ℕ)",
            f"{indent}      • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} {g} {h}",
            f"{indent}          - ramanujanGcdClassWindowAverageRat X0 {q2} {h}",
            f"{indent}              * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q} {g}",
            f"{indent}          - ramanujanGcdClassWindowAverageRat X0 {q} {g}",
            f"{indent}              * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q2} {h}",
            f"{indent}          + ramanujanGcdClassWindowAverageRat X0 {q} {g}",
            f"{indent}              * ramanujanGcdClassWindowAverageRat X0 {q2} {h}",
            f"{indent}              * evenRamanujanBlockCountRat {q} {q2}))",
        ]

    def emit_large_top_level_pair_proof() -> None:
        prefix = name

        def support(suffix: str) -> str:
            return f"{prefix}_{suffix}"

        def emit_block_periodic_count_theorem(
            *,
            theorem_name: str,
            q0: int,
            g0: int,
            expected: int,
        ) -> None:
            print(
                f"theorem {theorem_name} : "
                f"rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q0} {g0} = ({expected} : ℚ) := by"
            )
            print("  native_decide")
            print()

        def emit_pair_resolved_count_theorem(
            *,
            theorem_name: str,
            g: int,
            h: int,
            expected: int,
        ) -> None:
            print(
                f"theorem {theorem_name} : "
                f"rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} {g} {h} = ({expected} : ℚ) := by"
            )
            print("  native_decide")
            print()

        print(f"theorem {support('divLeft')} : Nat.divisors {q} = ({lean_nat_list(divs_q)} : List ℕ).toFinset := by")
        print("  decide")
        print()
        print(f"theorem {support('divRight')} : Nat.divisors {q2} = ({lean_nat_list(divs_q2)} : List ℕ).toFinset := by")
        print("  decide")
        print()
        for g in divs_q:
            v = exact_ctx["gcd_coeff_by_q"][q][g]
            print(f"theorem {support(f'coeffLeft_{g}')} : ramanujanGcdClassCoeffRat {q} {g} = {fraction_to_q_literal(v)} := by")
            print("  native_decide")
            print()
        for h in divs_q2:
            v = exact_ctx["gcd_coeff_by_q"][q2][h]
            print(f"theorem {support(f'coeffRight_{h}')} : ramanujanGcdClassCoeffRat {q2} {h} = {fraction_to_q_literal(v)} := by")
            print("  native_decide")
            print()
        for g in divs_q:
            v = exact_ctx["avg_by_q"][q][g]
            print(f"theorem {support(f'avgLeft_{g}')} : ramanujanGcdClassWindowAverageRat X0 {q} {g} = {fraction_to_q_literal(v)} := by")
            print("  native_decide")
            print()
        for h in divs_q2:
            v = exact_ctx["avg_by_q"][q2][h]
            print(f"theorem {support(f'avgRight_{h}')} : ramanujanGcdClassWindowAverageRat X0 {q2} {h} = {fraction_to_q_literal(v)} := by")
            print("  native_decide")
            print()
        for g in divs_q:
            v = gcd_class_count_in_even_progression(q, g, first_even, even_count, exact_ctx)
            emit_block_periodic_count_theorem(theorem_name=support(f"blockLeft_{g}"), q0=q, g0=g, expected=v)
        for h in divs_q2:
            v = gcd_class_count_in_even_progression(q2, h, first_even, even_count, exact_ctx)
            emit_block_periodic_count_theorem(theorem_name=support(f"blockRight_{h}"), q0=q2, g0=h, expected=v)
        for g in divs_q:
            for h in divs_q2:
                v = gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, exact_ctx)
                emit_pair_resolved_count_theorem(theorem_name=support(f"pair_{g}_{h}"), g=g, h=h, expected=v)

        full_blocks = (H + 1) // block_period(q, q2)
        even_count_rat = Fraction(even_count, 1)
        row_values: dict[int, Fraction] = {g: Fraction(0, 1) for g in divs_q}
        for g in divs_q:
            avg_g = exact_ctx["avg_by_q"][q][g]
            left = Fraction(gcd_class_count_in_even_progression(q, g, first_even, even_count, exact_ctx), 1)
            c_g = exact_ctx["gcd_coeff_by_q"][q][g]
            for h in divs_q2:
                avg_h = exact_ctx["avg_by_q"][q2][h]
                right = Fraction(gcd_class_count_in_even_progression(q2, h, first_even, even_count, exact_ctx), 1)
                pair = Fraction(
                    gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, exact_ctx),
                    1,
                )
                c_h = exact_ctx["gcd_coeff_by_q"][q2][h]
                centered_full_block = pair - avg_h * left - avg_g * right + avg_g * avg_h * even_count_rat
                term_value = c_g * c_h * Fraction(full_blocks, 1) * centered_full_block
                row_values[g] += term_value
                print(f"theorem {support(f'term_{g}_{h}')} :")
                for line in term_expr_lines(g, h, indent="    "):
                    print(line)
                print(f"      = {fraction_to_q_literal(term_value)} := by")
                print("  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,")
                print(
                    f"    {support(f'coeffLeft_{g}')}, {support(f'coeffRight_{h}')}, "
                    f"{support(f'avgLeft_{g}')}, {support(f'avgRight_{h}')},"
                )
                print(
                    f"    {support(f'blockLeft_{g}')}, {support(f'blockRight_{h}')}, "
                    f"{support(f'pair_{g}_{h}')}]"
                )
                print()
        for g in divs_q:
            print(f"theorem {support(f'row_{g}')} :")
            print(f"    (∑ h ∈ Nat.divisors {q2},")
            for line in term_expr_lines(g, "h", indent="      "):
                print(line)
            print(f"    ) = {fraction_to_q_literal(row_values[g])} := by")
            term_supports = [support(f"term_{g}_{h}") for h in divs_q2]
            print("  norm_num [" + ", ".join([support("divRight")] + term_supports) + "]")
            print()

        print(f"theorem {name}_centeredTerm :")
        print(f"    centeredRamanujanPairPeriodicMainTermRat X0 {q} {q2} = {fraction_to_q_literal(centered_term)} := by")
        print("  unfold centeredRamanujanPairPeriodicMainTermRat")
        row_supports = [support(f"row_{g}") for g in divs_q]
        print(f"  rw [{support('divLeft')}]")
        print("  simp [List.toFinset_cons, List.toFinset_nil, Finset.sum_insert,")
        print("    " + ", ".join(row_supports) + "]")
        print("  norm_num")
        print()
        print(f"theorem {name}_orderedSummand :")
        print(f"    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk {q} {q2}) = {fraction_to_q_literal(summand_value)} := by")
        print(f"  have hneq : {q} ≠ {q2} := by")
        print("    norm_num")
        print(f"  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat {q} = {fraction_to_q_literal(coeff_q)} := by")
        print("    native_decide")
        print(f"  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat {q2} = {fraction_to_q_literal(coeff_q2)} := by")
        print("    native_decide")
        print(
            f"  have hvalue : ({fraction_to_q_literal(coeff_q)}) * ({fraction_to_q_literal(coeff_q2)}) "
            f"* ({fraction_to_q_literal(centered_term)}) = {fraction_to_q_literal(summand_value)} := by"
        )
        print("    norm_num")
        print("  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue")
        print("    hneq hCoeffLeft hCoeffRight")
        print(f"    {name}_centeredTerm")
        print("    hvalue")
        print()

    if force_top_level_helpers or len(divs_q) * len(divs_q2) > 48:
        emit_large_top_level_pair_proof()
        return

    print(f"theorem {name}_centeredTerm :")
    print(f"    centeredRamanujanPairPeriodicMainTermRat X0 {q} {q2} = {fraction_to_q_literal(centered_term)} := by")
    print(f"  have hDivLeft : Nat.divisors {q} = ({lean_nat_list(divs_q)} : List ℕ).toFinset := by")
    print("    decide")
    print(f"  have hDivRight : Nat.divisors {q2} = ({lean_nat_list(divs_q2)} : List ℕ).toFinset := by")
    print("    decide")
    for g in divs_q:
        v = exact_ctx["gcd_coeff_by_q"][q][g]
        print(f"  have hCoeffLeft_{g} : ramanujanGcdClassCoeffRat {q} {g} = {fraction_to_q_literal(v)} := by")
        print("    native_decide")
    for h in divs_q2:
        v = exact_ctx["gcd_coeff_by_q"][q2][h]
        print(f"  have hCoeffRight_{h} : ramanujanGcdClassCoeffRat {q2} {h} = {fraction_to_q_literal(v)} := by")
        print("    native_decide")
    for g in divs_q:
        v = exact_ctx["avg_by_q"][q][g]
        print(f"  have hAvgLeft_{g} : ramanujanGcdClassWindowAverageRat X0 {q} {g} = {fraction_to_q_literal(v)} := by")
        print("    native_decide")
    for h in divs_q2:
        v = exact_ctx["avg_by_q"][q2][h]
        print(f"  have hAvgRight_{h} : ramanujanGcdClassWindowAverageRat X0 {q2} {h} = {fraction_to_q_literal(v)} := by")
        print("    native_decide")
    for g in divs_q:
        v = gcd_class_count_in_even_progression(q, g, first_even, even_count, exact_ctx)
        emit_block_periodic_count_proof(theorem_name=f"hBlockLeft_{g}", q0=q, g0=g, expected=v)
    for h in divs_q2:
        v = gcd_class_count_in_even_progression(q2, h, first_even, even_count, exact_ctx)
        emit_block_periodic_count_proof(theorem_name=f"hBlockRight_{h}", q0=q2, g0=h, expected=v)
    for g in divs_q:
        for h in divs_q2:
            v = gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, exact_ctx)
            emit_pair_resolved_count_proof(theorem_name=f"hPair_{g}_{h}", g=g, h=h, expected=v)
    full_blocks = (H + 1) // block_period(q, q2)
    even_count_rat = Fraction(even_count, 1)
    print("  let T : ℕ → ℕ → ℚ := fun g h =>")
    print(f"    ramanujanGcdClassCoeffRat {q} g * ramanujanGcdClassCoeffRat {q2} h")
    print(f"      * ((((H + 1) / centeredRamanujanPairBlockPeriod {q} {q2}) : ℕ)")
    print(f"          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} g h")
    print(f"              - ramanujanGcdClassWindowAverageRat X0 {q2} h")
    print(f"                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q} g")
    print(f"              - ramanujanGcdClassWindowAverageRat X0 {q} g")
    print(f"                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q2} h")
    print(f"              + ramanujanGcdClassWindowAverageRat X0 {q} g")
    print(f"                  * ramanujanGcdClassWindowAverageRat X0 {q2} h")
    print(f"                  * evenRamanujanBlockCountRat {q} {q2}))")
    term_names_by_g: dict[int, list[str]] = {g: [] for g in divs_q}
    row_values: dict[int, Fraction] = {g: Fraction(0, 1) for g in divs_q}
    for g in divs_q:
        avg_g = exact_ctx["avg_by_q"][q][g]
        left = Fraction(gcd_class_count_in_even_progression(q, g, first_even, even_count, exact_ctx), 1)
        c_g = exact_ctx["gcd_coeff_by_q"][q][g]
        for h in divs_q2:
            avg_h = exact_ctx["avg_by_q"][q2][h]
            right = Fraction(gcd_class_count_in_even_progression(q2, h, first_even, even_count, exact_ctx), 1)
            pair = Fraction(
                gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, exact_ctx),
                1,
            )
            c_h = exact_ctx["gcd_coeff_by_q"][q2][h]
            centered_full_block = pair - avg_h * left - avg_g * right + avg_g * avg_h * even_count_rat
            term_value = c_g * c_h * Fraction(full_blocks, 1) * centered_full_block
            term_name = f"hTerm_{g}_{h}"
            term_names_by_g[g].append(term_name)
            row_values[g] += term_value
            print(f"  have {term_name} :")
            print(f"      T {g} {h} = {fraction_to_q_literal(term_value)} := by")
            print("    dsimp [T]")
            print("    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,")
            print(
                f"      hCoeffLeft_{g}, hCoeffRight_{h}, hAvgLeft_{g}, hAvgRight_{h}, "
                f"hBlockLeft_{g}, hBlockRight_{h}, hPair_{g}_{h}]"
            )
    row_names: list[str] = []
    for g in divs_q:
        row_name = f"hRow_{g}"
        row_names.append(row_name)
        print(f"  have {row_name} :")
        print(f"      (∑ h ∈ Nat.divisors {q2}, T {g} h) = {fraction_to_q_literal(row_values[g])} := by")
        print("    norm_num [" + ", ".join(["hDivRight"] + term_names_by_g[g]) + "]")
    simp_args = [
        "centeredRamanujanPairBlockPeriod",
        "evenRamanujanBlockCountRat",
        "H",
        "hDivLeft",
        "hDivRight",
    ]
    simp_args.extend([f"hCoeffLeft_{g}" for g in divs_q])
    simp_args.extend([f"hCoeffRight_{h}" for h in divs_q2])
    simp_args.extend([f"hAvgLeft_{g}" for g in divs_q])
    simp_args.extend([f"hAvgRight_{h}" for h in divs_q2])
    simp_args.extend([f"hBlockLeft_{g}" for g in divs_q])
    simp_args.extend([f"hBlockRight_{h}" for h in divs_q2])
    simp_args.extend([f"hPair_{g}_{h}" for g in divs_q for h in divs_q2])
    print("  unfold centeredRamanujanPairPeriodicMainTermRat")
    print(f"  change (∑ g ∈ Nat.divisors {q}, ∑ h ∈ Nat.divisors {q2}, T g h) = {fraction_to_q_literal(centered_term)}")
    print("  rw [hDivLeft]")
    print("  simp [List.toFinset_cons, List.toFinset_nil, Finset.sum_insert,")
    print("    " + ", ".join(row_names) + "]")
    print("  norm_num")
    print()
    print(f"theorem {name}_orderedSummand :")
    print(f"    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk {q} {q2}) = {fraction_to_q_literal(summand_value)} := by")
    print(f"  have hneq : {q} ≠ {q2} := by")
    print("    norm_num")
    print(f"  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat {q} = {fraction_to_q_literal(coeff_q)} := by")
    print("    native_decide")
    print(f"  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat {q2} = {fraction_to_q_literal(coeff_q2)} := by")
    print("    native_decide")
    print(
        f"  have hvalue : ({fraction_to_q_literal(coeff_q)}) * ({fraction_to_q_literal(coeff_q2)}) "
        f"* ({fraction_to_q_literal(centered_term)}) = {fraction_to_q_literal(summand_value)} := by"
    )
    print("    norm_num")
    print("  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue")
    print("    hneq hCoeffLeft hCoeffRight")
    print(f"    {name}_centeredTerm")
    print("    hvalue")
    print()


def centered_ramanujan_pair_boundary_term_rat_cached(
    X: int,
    q: int,
    q2: int,
    ctx: dict[str, object],
) -> Fraction:
    divisors_by_q = ctx["divisors_by_q"]
    avg_by_q = ctx["avg_by_q"]
    gcd_coeff_by_q = ctx["gcd_coeff_by_q"]

    divs_q = divisors_by_q[q]
    divs_q2 = divisors_by_q[q2]
    avg_q = avg_by_q[q]
    avg_q2 = avg_by_q[q2]
    coeff_q = gcd_coeff_by_q[q]
    coeff_q2 = gcd_coeff_by_q[q2]

    P = block_period(q, q2)
    m = (H + 1) // P
    r = (H + 1) % P
    if r == 0:
        return Fraction(0, 1)

    even_ns = [X + m * P + k for k in range(r) if (X + m * P + k) % 2 == 0]
    out = Fraction(0, 1)
    for g in divs_q:
        c_g = coeff_q[g]
        avg_g = avg_q[g]
        for h in divs_q2:
            c_h = coeff_q2[h]
            avg_h = avg_q2[h]
            rem = Fraction(0, 1)
            for N in even_ns:
                ind_g = Fraction(1 if math.gcd(q, N) == g else 0, 1)
                ind_h = Fraction(1 if math.gcd(q2, N) == h else 0, 1)
                rem += (ind_g - avg_g) * (ind_h - avg_h)
            out += c_g * c_h * rem
    return out


def surrogate_boundary_pair_contribution_rat_cached(
    X: int,
    q: int,
    q2: int,
    ctx: dict[str, object],
) -> Fraction:
    if q == q2:
        return Fraction(0, 1)
    coeff_rat = ctx["coeff_rat"]
    return (
        coeff_rat[q]
        * coeff_rat[q2]
        * centered_ramanujan_pair_boundary_term_rat_cached(X, q, q2, ctx)
    )


def _boundary_exact_parallel_eval_chunk(
    chunk_start: int,
    chunk_end: int,
    chunk_blocks: list[tuple[tuple[int, int], int]],
) -> tuple[dict[str, object], float]:
    g = _BOUNDARY_EXACT_PARALLEL_GLOBALS
    X = int(g["X"])
    exact_ctx = g["exact_ctx"]
    total_pairs = int(g["total_pairs"])
    total_active_blocks = int(g["total_active_blocks"])
    active_support_card = int(g["active_support_card"])
    progress = bool(g["progress"])
    progress_every = int(g["progress_every"])
    block_progress_every = min(
        max(1, min(max(progress_every, 1), max(1, len(chunk_blocks) // 10))),
        50_000,
    )
    processed = 0
    started = time.time()
    chunk_total = Fraction(0, 1)
    chunk_abs_total = Fraction(0, 1)
    for pattern, G in chunk_blocks:
        m, n = pattern
        q = G * m
        q2 = G * n
        val = 2 * surrogate_boundary_pair_contribution_rat_cached(X, q, q2, exact_ctx)
        abs_val = abs(val)
        chunk_total += val
        chunk_abs_total += abs_val
        processed += 1
        if progress and processed % block_progress_every == 0:
            elapsed = time.time() - started
            print(
                f"[boundary-signed-split-exact:worker] processed_blocks={processed}/{len(chunk_blocks)} "
                f"chunk=[{chunk_start},{chunk_end}) elapsed={elapsed:.1f}s",
                file=sys.stderr,
                flush=True,
            )

    elapsed_sec = time.time() - started
    payload = {
        "mode": "boundary-signed-split-exact-chunk",
        "X": X,
        "active_support_card": active_support_card,
        "active_ordered_pairs": total_pairs,
        "total_active_blocks": total_active_blocks,
        "block_range": [chunk_start, chunk_end],
        "start": chunk_start,
        "end": chunk_end,
        "chunk_total_num": chunk_total.numerator,
        "chunk_total_den": chunk_total.denominator,
        "chunk_abs_total_num": chunk_abs_total.numerator,
        "chunk_abs_total_den": chunk_abs_total.denominator,
        "elapsed_sec": elapsed_sec,
    }
    return payload, elapsed_sec


def _boundary_exact_parallel_worker(task: tuple[int, int]) -> dict[str, object]:
    g = _BOUNDARY_EXACT_PARALLEL_GLOBALS
    checkpoint_dir = str(g["checkpoint_dir"])
    skip_existing = bool(g["skip_existing_chunks"])
    start_ref = int(g["start"])
    all_blocks = g["all_blocks"]
    chunk_start, chunk_end = task
    out_path = os.path.join(
        checkpoint_dir,
        f"boundary_active_exact_chunk_{chunk_start:07d}_{chunk_end:07d}.json",
    )
    if skip_existing and os.path.exists(out_path):
        return {
            "status": "skipped",
            "chunk_start": chunk_start,
            "chunk_end": chunk_end,
            "out_path": out_path,
        }
    payload, elapsed_sec = _boundary_exact_parallel_eval_chunk(
        chunk_start,
        chunk_end,
        all_blocks[chunk_start - start_ref:chunk_end - start_ref],
    )
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, sort_keys=True)
    return {
        "status": "written",
        "chunk_start": chunk_start,
        "chunk_end": chunk_end,
        "out_path": out_path,
        "elapsed_sec": elapsed_sec,
        "chunk_total_num": payload["chunk_total_num"],
        "chunk_total_den": payload["chunk_total_den"],
    }


def _periodic_main_exact_parallel_eval_chunk(
    chunk_start: int,
    chunk_end: int,
    chunk_pairs: list[tuple[int, int]],
) -> tuple[dict[str, object], float]:
    g = _PERIODIC_MAIN_EXACT_PARALLEL_GLOBALS
    X = int(g["X"])
    exact_ctx = g["exact_ctx"]
    active_support_card = int(g["active_support_card"])
    total_unordered_pairs = int(g["total_unordered_pairs"])
    progress = bool(g["progress"])
    progress_every = int(g["progress_every"])
    pair_progress_every = min(
        max(1, min(max(progress_every, 1), max(1, len(chunk_pairs) // 10))),
        50_000,
    )
    processed = 0
    active_nonzero_pairs = 0
    started = time.time()
    chunk_total = Fraction(0, 1)
    chunk_abs_total = Fraction(0, 1)
    nonzero_records = []
    for q, q2 in chunk_pairs:
        val = centered_ramanujan_pair_periodic_main_term_rat_cached(X, q, q2, exact_ctx)
        if val != 0:
            signed_val = 2 * val
            active_nonzero_pairs += 1
            chunk_total += signed_val
            chunk_abs_total += abs(signed_val)
            nonzero_records.append({
                "q": q,
                "q2": q2,
                "signed_num": signed_val.numerator,
                "signed_den": signed_val.denominator,
            })
        processed += 1
        if progress and processed % pair_progress_every == 0:
            elapsed = time.time() - started
            print(
                f"[periodic-main-exact:worker] processed_pairs={processed}/{len(chunk_pairs)} "
                f"chunk=[{chunk_start},{chunk_end}) elapsed={elapsed:.1f}s",
                file=sys.stderr,
                flush=True,
            )

    elapsed_sec = time.time() - started
    payload = {
        "mode": "periodic-main-exact-chunk",
        "X": X,
        "active_support_card": active_support_card,
        "total_unordered_pairs": total_unordered_pairs,
        "pair_range": [chunk_start, chunk_end],
        "start": chunk_start,
        "end": chunk_end,
        "active_nonzero_pairs": active_nonzero_pairs,
        "chunk_total_num": chunk_total.numerator,
        "chunk_total_den": chunk_total.denominator,
        "chunk_abs_total_num": chunk_abs_total.numerator,
        "chunk_abs_total_den": chunk_abs_total.denominator,
        "nonzero_records": nonzero_records,
        "elapsed_sec": elapsed_sec,
    }
    return payload, elapsed_sec


def _periodic_main_exact_parallel_worker(task: tuple[int, int]) -> dict[str, object]:
    g = _PERIODIC_MAIN_EXACT_PARALLEL_GLOBALS
    checkpoint_dir = str(g["checkpoint_dir"])
    skip_existing = bool(g["skip_existing_chunks"])
    start_ref = int(g["start"])
    all_pairs = g["all_pairs"]
    chunk_start, chunk_end = task
    out_path = os.path.join(
        checkpoint_dir,
        f"periodic_main_exact_chunk_{chunk_start:07d}_{chunk_end:07d}.json",
    )
    if skip_existing and os.path.exists(out_path):
        return {
            "status": "skipped",
            "chunk_start": chunk_start,
            "chunk_end": chunk_end,
            "out_path": out_path,
        }
    payload, elapsed_sec = _periodic_main_exact_parallel_eval_chunk(
        chunk_start,
        chunk_end,
        all_pairs[chunk_start - start_ref:chunk_end - start_ref],
    )
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, sort_keys=True)
    return {
        "status": "written",
        "chunk_start": chunk_start,
        "chunk_end": chunk_end,
        "out_path": out_path,
        "elapsed_sec": elapsed_sec,
        "chunk_total_num": payload["chunk_total_num"],
        "chunk_total_den": payload["chunk_total_den"],
    }


def definitely_zero_surrogate_boundary_pair(q: int, q2: int) -> bool:
    if q == q2:
        return True
    # On the even window, q=1 and q=2 give constant Ramanujan observables, so centered terms vanish.
    if q in (1, 2) or q2 in (1, 2):
        return True
    # If the boundary remainder length is zero, the boundary term vanishes identically.
    return ((H + 1) % block_period(q, q2)) == 0


def canonical_pattern_and_g(q: int, q2: int) -> tuple[tuple[int, int], int]:
    G = math.gcd(q, q2)
    m = q // G
    n = q2 // G
    return ((m, n) if m <= n else (n, m), G)


def build_active_boundary_block_table(
    block_scope: list[int],
    *,
    progress: bool = False,
    progress_every: int = 10000,
) -> tuple[dict[tuple[tuple[int, int], int], int], int]:
    pair_count_by_block: dict[tuple[tuple[int, int], int], int] = defaultdict(int)
    total_pairs = len(block_scope) * max(len(block_scope) - 1, 0)
    processed = 0
    started = time.time()
    for q in block_scope:
        for q2 in block_scope:
            if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                continue
            processed += 1
            pair_count_by_block[canonical_pattern_and_g(q, q2)] += 1
            if progress and processed % progress_every == 0:
                elapsed = time.time() - started
                print(
                    f"[active-blocks] processed={processed}/{total_pairs} "
                    f"blocks={len(pair_count_by_block)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )
    return dict(pair_count_by_block), total_pairs


def v2_adic(n: int) -> int:
    out = 0
    while n % 2 == 0 and n > 0:
        n //= 2
        out += 1
    return out


def odd_radical_from_spf(n: int, spf: list[int]) -> int:
    if n <= 1:
        return 1
    fac = factorization(n, spf)
    out = 1
    for p, _ in fac:
        if p != 2:
            out *= p
    return out


def prime_support_from_spf(n: int, spf: list[int]) -> tuple[int, ...]:
    if n <= 1:
        return ()
    return tuple(sorted(factorization(n, spf).keys()))


def evaluate_exact_boundary_pattern_family(
    *,
    X: int,
    target_pattern: tuple[int, int],
    family_scope: list[int],
    pair_count_by_block: dict[tuple[tuple[int, int], int], int],
    total_pairs: int,
    mu: list[int],
    phi: list[int],
    spf: list[int],
    even_window_card: int,
    progress: bool,
    progress_every: int,
) -> dict[str, object]:
    family_blocks = sorted(
        [block for block in pair_count_by_block if block[0] == target_pattern],
        key=lambda block: block[1],
    )
    if not family_blocks:
        raise SystemExit(f"no active boundary blocks found for pattern {target_pattern[0]}:{target_pattern[1]}")

    q_needed_exact: set[int] = set()
    for _, G in family_blocks:
        q_needed_exact.add(G * target_pattern[0])
        q_needed_exact.add(G * target_pattern[1])

    exact_ctx = build_surrogate_boundary_exact_context(
        X, mu, phi, spf, even_window_card, sorted(q_needed_exact),
        progress=progress,
        progress_every_q=max(1, progress_every),
    )

    family_signed = Fraction(0, 1)
    family_abs = Fraction(0, 1)
    elapsed_by_block: dict[tuple[tuple[int, int], int], float] = {}
    signed_by_block: dict[tuple[tuple[int, int], int], Fraction] = {}
    abs_by_block: dict[tuple[tuple[int, int], int], Fraction] = {}
    g_prime_support_signed: dict[tuple[int, ...], Fraction] = defaultdict(lambda: Fraction(0, 1))
    g_prime_support_abs: dict[tuple[int, ...], Fraction] = defaultdict(lambda: Fraction(0, 1))
    g_prime_support_count: Counter[tuple[int, ...]] = Counter()

    started = time.time()
    for i, block in enumerate(family_blocks, start=1):
        _, G = block
        q = G * target_pattern[0]
        q2 = G * target_pattern[1]
        t0 = time.perf_counter()
        val = 2 * surrogate_boundary_pair_contribution_rat_cached(X, q, q2, exact_ctx)
        elapsed = time.perf_counter() - t0
        abs_val = abs(val)
        elapsed_by_block[block] = elapsed
        signed_by_block[block] = val
        abs_by_block[block] = abs_val
        family_signed += val
        family_abs += abs_val
        sig = prime_support_from_spf(G, spf)
        g_prime_support_signed[sig] += val
        g_prime_support_abs[sig] += abs_val
        g_prime_support_count[sig] += 1
        if progress and i % max(1, min(progress_every, 200)) == 0:
            elapsed_total = time.time() - started
            print(
                f"[boundary-pattern-family-exact] pattern={target_pattern[0]}:{target_pattern[1]} "
                f"processed_G={i}/{len(family_blocks)} elapsed={elapsed_total:.1f}s",
                file=sys.stderr,
                flush=True,
            )

    total_elapsed = time.time() - started
    pair_mass = sum(pair_count_by_block[block] for block in family_blocks)
    return {
        "pattern": target_pattern,
        "scope_card": len(family_scope),
        "total_pairs": total_pairs,
        "g_count": len(family_blocks),
        "pair_mass": pair_mass,
        "signed": family_signed,
        "abs": family_abs,
        "elapsed_sec": total_elapsed,
        "elapsed_by_block": elapsed_by_block,
        "signed_by_block": signed_by_block,
        "abs_by_block": abs_by_block,
        "g_prime_support_signed": g_prime_support_signed,
        "g_prime_support_abs": g_prime_support_abs,
        "g_prime_support_count": g_prime_support_count,
        "family_blocks": family_blocks,
    }


def parse_selected_patterns(raw_patterns: list[str]) -> set[tuple[int, int]]:
    selected_patterns: set[tuple[int, int]] = set()
    for raw in raw_patterns:
        if ":" not in raw:
            raise SystemExit(f"invalid pattern {raw!r}; expected m:n")
        left, right = raw.split(":", 1)
        m = int(left)
        n = int(right)
        if m <= 0 or n <= 0:
            raise SystemExit(f"invalid pattern {raw!r}; entries must be positive")
        selected_patterns.add((m, n) if m <= n else (n, m))
    return selected_patterns


def parse_selected_products(raw_products: list[int]) -> set[int]:
    selected_products: set[int] = set()
    for prod in raw_products:
        if prod <= 0:
            raise SystemExit(f"invalid product class {prod!r}; entries must be positive")
        selected_products.add(prod)
    return selected_products


def boundary_pattern_is_excluded(
    pattern: tuple[int, int],
    excluded_patterns: set[tuple[int, int]],
    excluded_products: set[int],
) -> bool:
    return pattern in excluded_patterns or (pattern[0] * pattern[1]) in excluded_products


def classify_signed_boundary_blocks(
    pair_count_by_block: dict[tuple[tuple[int, int], int], int],
    signed_by_block: dict[tuple[tuple[int, int], int], float],
    abs_by_block: dict[tuple[tuple[int, int], int], float],
    *,
    top_remove: int,
    selected_patterns: set[tuple[int, int]],
) -> dict[str, object]:
    ranked_blocks = sorted(
        signed_by_block.keys(),
        key=lambda block: (
            abs_by_block[block],
            abs(signed_by_block[block]),
            pair_count_by_block[block],
            -block[1],
            -block[0][0],
            -block[0][1],
        ),
        reverse=True,
    )
    top_global_blocks = set(ranked_blocks[:max(top_remove, 0)])
    expanded_family_blocks = {
        block for block in ranked_blocks[max(top_remove, 0):]
        if block[0] in selected_patterns
    }
    selected_blocks = top_global_blocks | expanded_family_blocks
    coherent_threshold = 1.0 - 1e-12
    coherent_leftover_blocks = [
        block for block in ranked_blocks
        if block not in selected_blocks
        and pair_count_by_block[block] == 2
        and ((abs(signed_by_block[block]) / abs_by_block[block]) if abs_by_block[block] else 0.0) >= coherent_threshold
    ]
    incoherent_leftover_blocks = [
        block for block in ranked_blocks
        if block not in selected_blocks and block not in coherent_leftover_blocks
    ]

    selected_signed = math.fsum(signed_by_block[block] for block in selected_blocks)
    selected_abs = math.fsum(abs_by_block[block] for block in selected_blocks)
    coh2_signed = math.fsum(signed_by_block[block] for block in coherent_leftover_blocks)
    coh2_abs = math.fsum(abs_by_block[block] for block in coherent_leftover_blocks)
    incoh_signed = math.fsum(signed_by_block[block] for block in incoherent_leftover_blocks)
    incoh_abs = math.fsum(abs_by_block[block] for block in incoherent_leftover_blocks)

    return {
        "ranked_blocks": ranked_blocks,
        "top_global_blocks": top_global_blocks,
        "expanded_family_blocks": expanded_family_blocks,
        "selected_blocks": selected_blocks,
        "coherent_leftover_blocks": coherent_leftover_blocks,
        "incoherent_leftover_blocks": incoherent_leftover_blocks,
        "selected_signed": selected_signed,
        "selected_abs": selected_abs,
        "coh2_signed": coh2_signed,
        "coh2_abs": coh2_abs,
        "incoh_signed": incoh_signed,
        "incoh_abs": incoh_abs,
    }


def build_surrogate_boundary_float_context(
    X: int,
    mu: list[int],
    phi: list[int],
    spf: list[int],
    even_window_card: int,
    support: list[int],
    progress: bool = False,
    progress_every_q: int = 500,
) -> dict[str, object]:
    coeff_float: dict[int, float] = {}
    divisors_by_q: dict[int, list[int]] = {}
    avg_by_q: dict[int, dict[int, float]] = {}
    gcd_coeff_by_q: dict[int, dict[int, float]] = {}

    started = time.time()
    for i, q in enumerate(support, start=1):
        coeff_float[q] = normalized_sigma_trunc_summand_real_coeff(q, mu, phi)
        fac_q = factorization(q, spf)
        divs_q = divisors_from_factorization(fac_q)
        divisors_by_q[q] = divs_q
        counts: dict[int, int] = defaultdict(int)
        start = X if X % 2 == 0 else X + 1
        for N in range(start, X + H + 1, 2):
            counts[math.gcd(q, N)] += 1
        avg_by_q[q] = {g: counts.get(g, 0) / float(even_window_card) for g in divs_q}
        gcd_coeff_by_q[q] = {
            g: ramanujan_gcd_class_coeff(q, g, mu, phi)
            for g in divs_q
        }
        if progress and (i % progress_every_q == 0 or i == len(support)):
            elapsed = time.time() - started
            print(
                f"[boundary-period:precompute] q={i}/{len(support)} elapsed={elapsed:.1f}s",
                file=sys.stderr,
                flush=True,
            )

    return {
        "coeff_float": coeff_float,
        "divisors_by_q": divisors_by_q,
        "avg_by_q": avg_by_q,
        "gcd_coeff_by_q": gcd_coeff_by_q,
        "mu": mu,
        "spf": spf,
        "divisor_list_cache": {},
        "divisibility_count_cache": {},
        "gcd_class_count_cache": {},
        "gcd_class_pair_count_cache": {},
    }


def surrogate_boundary_pair_contribution_float_cached(
    X: int,
    q: int,
    q2: int,
    ctx: dict[str, object],
) -> float:
    if q == q2:
        return 0.0
    if definitely_zero_surrogate_boundary_pair(q, q2):
        return 0.0
    coeff_float = ctx["coeff_float"]
    divisors_by_q = ctx["divisors_by_q"]
    avg_by_q = ctx["avg_by_q"]
    gcd_coeff_by_q = ctx["gcd_coeff_by_q"]

    divs_q = divisors_by_q[q]
    divs_q2 = divisors_by_q[q2]
    avg_q = avg_by_q[q]
    avg_q2 = avg_by_q[q2]
    coeff_q = gcd_coeff_by_q[q]
    coeff_q2 = gcd_coeff_by_q[q2]

    P = block_period(q, q2)
    first_even, even_count = boundary_remainder_even_progression(X, q, q2)
    if even_count == 0:
        return 0.0

    out = 0.0
    for g in divs_q:
        c_g = coeff_q[g]
        avg_g = avg_q[g]
        left = float(gcd_class_count_in_even_progression(q, g, first_even, even_count, ctx))
        for h in divs_q2:
            c_h = coeff_q2[h]
            avg_h = avg_q2[h]
            right = float(gcd_class_count_in_even_progression(q2, h, first_even, even_count, ctx))
            pair = float(gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, ctx))
            rem = pair - avg_h * left - avg_g * right + avg_g * avg_h * float(even_count)
            out += c_g * c_h * rem
    return coeff_float[q] * coeff_float[q2] * out


def centered_boundary_core_float_detail(
    X: int,
    q: int,
    q2: int,
    ctx: dict[str, object],
) -> tuple[float, float, list[tuple[float, int, int, float]]]:
    """
    Return detailed centered boundary core data for one ordered pair.

    Output:
      - signed centered `(g,h)` core sum
      - absolute `(g,h)` majorant, i.e. sum of abs individual centered `(g,h)` contributions
      - list of `(abs_term, g, h, signed_term)` records, sorted later by caller
    """
    divisors_by_q = ctx["divisors_by_q"]
    avg_by_q = ctx["avg_by_q"]
    gcd_coeff_by_q = ctx["gcd_coeff_by_q"]

    divs_q = divisors_by_q[q]
    divs_q2 = divisors_by_q[q2]
    avg_q = avg_by_q[q]
    avg_q2 = avg_by_q[q2]
    coeff_q = gcd_coeff_by_q[q]
    coeff_q2 = gcd_coeff_by_q[q2]

    P = block_period(q, q2)
    first_even, even_count = boundary_remainder_even_progression(X, q, q2)
    if even_count == 0:
        return 0.0, 0.0, []

    core = 0.0
    abs_core = 0.0
    detail: list[tuple[float, int, int, float]] = []
    for g in divs_q:
        c_g = coeff_q[g]
        avg_g = avg_q[g]
        left = float(gcd_class_count_in_even_progression(q, g, first_even, even_count, ctx))
        for h in divs_q2:
            c_h = coeff_q2[h]
            avg_h = avg_q2[h]
            right = float(gcd_class_count_in_even_progression(q2, h, first_even, even_count, ctx))
            pair = float(gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, ctx))
            rem = pair - avg_h * left - avg_g * right + avg_g * avg_h * float(even_count)
            term = c_g * c_h * rem
            core += term
            abs_core += abs(term)
            if term != 0.0:
                detail.append((abs(term), g, h, term))
    return core, abs_core, detail


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Direct truncation/periodic-main/boundary audit for surrogate or true-series normalization."
    )
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--q-max-active", type=int, default=(H + 1) // 2)
    ap.add_argument("--true-series", action="store_true",
                    help="Use a numerical approximation to the true Lean-side C2 from the odd-prime Euler product.")
    ap.add_argument("--true-prime-cutoff", type=int, default=1_000_000,
                    help="Odd-prime cutoff used in the numerical Euler-product approximation for --true-series.")
    ap.add_argument("--diag-only", action="store_true",
                    help="Only compute diagonal data; skip periodic-main and boundary passes.")
    ap.add_argument("--diag-breakdown", action="store_true",
                    help="Print per-q diagonal summand-energy diagnostics on the true coefficient support.")
    ap.add_argument("--diag-top", type=int, default=30,
                    help="How many top-q diagonal energies to print in breakdown mode.")
    ap.add_argument("--emit-pointwise-certificate", action="store_true",
                    help="Print the concrete X-point certificate data for the direct Route A wrapper.")
    ap.add_argument("--emit-lean-checkle", action="store_true",
                    help="Emit a ready-to-paste Lean MajorArcCertChecker `CheckLE` payload for the current surrogate audit values.")
    ap.add_argument("--emit-diag-tail-rat-total", action="store_true",
                    help="Emit the exact surrogate diagonal tail rational total at the current X as a Lean ℚ literal.")
    ap.add_argument("--emit-diag-single-q-rat-data", type=int, default=-1,
                    help="Emit exact per-q rational certificate data for one diagonal summand.")
    ap.add_argument("--emit-diag-tail-rat-chunks", action="store_true",
                    help="Emit chunked exact surrogate diagonal-tail rational totals as Lean ℚ literals.")
    ap.add_argument("--diag-tail-chunk-size", type=int, default=500,
                    help="Chunk size for --emit-diag-tail-rat-chunks.")
    ap.add_argument("--emit-diag-tail-rat-chunk-index", type=int, default=-1,
                    help="Emit one exact surrogate diagonal-tail chunk by index; requires --diag-tail-chunk-size.")
    ap.add_argument("--emit-diag-tail-rat-subchunks-for-chunk-index", type=int, default=-1,
                    help="Emit Lean-ready exact surrogate diagonal-tail subchunk payloads for one chunk index; requires --diag-tail-chunk-size.")
    ap.add_argument("--diag-tail-subchunk-size", type=int, default=1000,
                    help="Subchunk size for --emit-diag-tail-rat-subchunks-for-chunk-index.")
    ap.add_argument("--emit-diag-tail-rat-one-subchunk-for-chunk-index", type=int, default=-1,
                    help="Emit Lean-ready exact surrogate diagonal-tail payload for one subchunk of one chunk; requires --diag-tail-subchunk-index and --diag-tail-chunk-size.")
    ap.add_argument("--diag-tail-subchunk-index", type=int, default=-1,
                    help="With --emit-diag-tail-rat-one-subchunk-for-chunk-index, choose the subchunk index inside the chunk.")
    ap.add_argument("--diag-tail-subchunk-start-offset", type=int, default=-1,
                    help="Optional explicit start offset inside the selected chunk for subchunk-based tail emitters.")
    ap.add_argument("--diag-tail-one-subchunk-part-size", type=int, default=0,
                    help="If positive, split the selected one-subchunk payload into smaller explicit part supports of this size.")
    ap.add_argument("--emit-diag-tail-direct-term-block-module-for-chunk-index", type=int, default=-1,
                    help="Emit a Lean module for direct term-certificate blocks inside one surrogate diagonal-tail subchunk.")
    ap.add_argument("--diag-tail-block-size", type=int, default=25,
                    help="Block size, in terms, for --emit-diag-tail-direct-term-block-module-for-chunk-index.")
    ap.add_argument("--diag-tail-block-start-index", type=int, default=0,
                    help="Starting block index inside the selected subchunk for --emit-diag-tail-direct-term-block-module-for-chunk-index.")
    ap.add_argument("--diag-tail-block-count", type=int, default=1,
                    help="Number of consecutive blocks to emit for --emit-diag-tail-direct-term-block-module-for-chunk-index.")
    ap.add_argument("--diag-tail-module-name", type=str, default="",
                    help="Optional output module basename for --emit-diag-tail-direct-term-block-module-for-chunk-index.")
    ap.add_argument("--emit-periodic-main-rat-total", action="store_true",
                    help="Emit the exact surrogate periodic-main rational total at the current X as a Lean ℚ literal.")
    ap.add_argument("--emit-boundary-pair-rat", nargs=2, type=int, metavar=("Q", "Q2"),
                    help="Emit the exact surrogate boundary pair contribution for one ordered pair as a Lean ℚ literal.")
    ap.add_argument("--emit-boundary-rat-total", action="store_true",
                    help="Emit the exact surrogate boundary rational total and nonzero ordered-pair count.")
    ap.add_argument("--emit-boundary-rat-terms", action="store_true",
                    help="Emit the finite nonzero ordered-pair rational term list for the surrogate boundary certificate.")
    ap.add_argument("--boundary-rat-scope", choices=["full", "active"], default="full",
                    help="Support scope for exact surrogate boundary export modes.")
    ap.add_argument("--include-terms", action="store_true",
                    help="With --emit-boundary-rat-total, also emit the full nonzero ordered-pair rational term list.")
    ap.add_argument("--progress", action="store_true",
                    help="Print stderr progress for exact rational boundary export modes.")
    ap.add_argument("--progress-every", type=int, default=10000,
                    help="Progress interval in ordered pairs for exact rational boundary export modes.")
    ap.add_argument("--pair-limit", type=int, default=0,
                    help="Optional ordered-pair cap for debugging exact rational boundary export modes (0 = no cap).")
    ap.add_argument("--checkpoint-json", type=str, default="",
                    help="Optional path for periodic JSON checkpoints during exact rational boundary export modes.")
    ap.add_argument("--boundary-zero-prune-report", action="store_true",
                    help="Print cheap structural survivor counts for surrogate boundary exact-certificate generation.")
    ap.add_argument("--boundary-period-group-report", action="store_true",
                    help="Group surrogate boundary pairs by P = 2*lcm(q,q') and report counts/proxies; float totals are computed only for the top groups.")
    ap.add_argument("--boundary-period-group-scope", choices=("active", "full"), default="active",
                    help="Support scope for --boundary-period-group-report. 'active' uses q <= (H+1)/2; 'full' uses all coefficient support.")
    ap.add_argument("--boundary-period-group-top", type=int, default=20,
                    help="How many top period groups to print in --boundary-period-group-report.")
    ap.add_argument("--boundary-pattern-report", action="store_true",
                    help="Group surrogate boundary pairs by unordered multiplier pattern (m:n) with q = Gm, q' = Gn.")
    ap.add_argument("--boundary-pattern-scope", choices=("active", "full"), default="active",
                    help="Support scope for --boundary-pattern-report. 'active' uses q <= (H+1)/2; 'full' uses all coefficient support.")
    ap.add_argument("--boundary-pattern-top", type=int, default=20,
                    help="How many top multiplier patterns to print in --boundary-pattern-report.")
    ap.add_argument("--boundary-pattern-top-g", type=int, default=5,
                    help="How many top G-values to print inside each top multiplier pattern.")
    ap.add_argument("--boundary-pattern-g-report", action="store_true",
                    help="Group surrogate boundary pairs by unordered multiplier pattern plus G = gcd(q,q').")
    ap.add_argument("--boundary-pattern-g-scope", choices=("active", "full"), default="active",
                    help="Support scope for --boundary-pattern-g-report. 'active' uses q <= (H+1)/2; 'full' uses all coefficient support.")
    ap.add_argument("--boundary-pattern-g-top", type=int, default=50,
                    help="How many top (pattern,G) blocks to print in --boundary-pattern-g-report.")
    ap.add_argument("--boundary-pattern-g-top-pairs", type=int, default=3,
                    help="How many top ordered pairs to print inside each top (pattern,G) block.")
    ap.add_argument("--boundary-pattern-g-cumulative", action="store_true",
                    help="With --boundary-pattern-g-report, print cumulative abs-mass shares for top (pattern,G) blocks.")
    ap.add_argument("--boundary-pattern-g-candidate-blocks", type=int, default=0,
                    help="How many (pattern,G) blocks to evaluate by float mass after proxy ranking (0 = use max(top*10, top)).")
    ap.add_argument("--boundary-pattern-g-tail-report", action="store_true",
                    help="After removing top (pattern,G) blocks, regroup the residual by multiplier pattern m:n.")
    ap.add_argument("--boundary-pattern-g-remove-top", type=int, default=0,
                    help="How many top (pattern,G) blocks to remove before forming the residual pattern report.")
    ap.add_argument("--boundary-pattern-tail-top", type=int, default=30,
                    help="How many residual multiplier patterns to print in --boundary-pattern-g-tail-report.")
    ap.add_argument("--boundary-pattern-family-detail", nargs=2, type=int, metavar=("M", "N"),
                    help="Detailed surrogate boundary report for one unordered multiplier pattern M:N after optional top-(pattern,G) removal.")
    ap.add_argument("--boundary-pattern-family-scope", choices=("active", "full"), default="active",
                    help="Support scope for --boundary-pattern-family-detail. 'active' uses q <= (H+1)/2; 'full' uses all coefficient support.")
    ap.add_argument("--boundary-pattern-family-top-g", type=int, default=20,
                    help="How many top G-values to print in --boundary-pattern-family-detail.")
    ap.add_argument("--boundary-pattern-family-cumulative", action="store_true",
                    help="With --boundary-pattern-family-detail, print cumulative abs-mass share by top G-values.")
    ap.add_argument("--boundary-pattern-family-exact", nargs=2, type=int, metavar=("M", "N"),
                    help="Evaluate one unordered multiplier pattern M:N exactly as a one-family boundary sum over G.")
    ap.add_argument("--boundary-pattern-family-exact-batch", nargs="*", default=[],
                    help="Evaluate several unordered multiplier patterns exactly, written as m:n, and emit one exact rational per family plus a combined total.")
    ap.add_argument("--boundary-selected-block-certificate-report", action="store_true",
                    help="Report selected global top (pattern,G) blocks plus fully expanded chosen residual families, and measure the leftover over the evaluated candidate pool.")
    ap.add_argument("--boundary-family-patterns", nargs="*", default=[],
                    help="Patterns to fully expand in --boundary-selected-block-certificate-report, written as m:n.")
    ap.add_argument("--boundary-selected-leftover-top", type=int, default=20,
                    help="How many top leftover residual patterns to print in --boundary-selected-block-certificate-report.")
    ap.add_argument("--boundary-selected-coherence-report", action="store_true",
                    help="With --boundary-selected-block-certificate-report, summarize leftover blocks by pair count and coherence.")
    ap.add_argument("--emit-boundary-selected-rat-certificate", action="store_true",
                    help="With --boundary-selected-block-certificate-report, also emit exact rational totals for selected/coherent-pair2/incoherent pieces over the evaluated candidate pool.")
    ap.add_argument("--coh2-formula-audit", action="store_true",
                    help="Audit a cheap theorem-facing majorant for the coherent pair-count-2 leftover blocks after the selected boundary block split.")
    ap.add_argument("--coh2-formula-top", type=int, default=30,
                    help="How many coherent pair-count-2 leftover blocks to print in --coh2-formula-audit.")
    ap.add_argument("--coh2-centered-core-audit", action="store_true",
                    help="Audit coherent pair-count-2 leftover blocks using the exact centered (g,h) core, and compare against crude divisor-sum majorants.")
    ap.add_argument("--coh2-centered-core-top-gh", type=int, default=8,
                    help="How many top centered divisor-pair contributions to print inside each top block in --coh2-centered-core-audit.")
    ap.add_argument("--coh2-signed-structure-report", action="store_true",
                    help="Report candidate-scope signed structure of the coherent pair-count-2 leftover blocks after the selected boundary block split.")
    ap.add_argument("--coh2-signed-structure-top-patterns", type=int, default=30,
                    help="How many signed coherent-pattern groups to print in --coh2-signed-structure-report.")
    ap.add_argument("--coh2-signed-structure-top-blocks", type=int, default=20,
                    help="How many top positive and top negative coherent blocks to print in --coh2-signed-structure-report.")
    ap.add_argument("--boundary-block-key-report", action="store_true",
                    help="Report active reversible-block key multiplicities to estimate cache and chunking potential before full signed evaluation.")
    ap.add_argument("--boundary-block-key-top", type=int, default=20,
                    help="How many top repeated keys to print per key family in --boundary-block-key-report.")
    ap.add_argument("--boundary-pattern-runtime-report", action="store_true",
                    help="Evaluate exact boundary contributions for the top active multiplier patterns and report per-pattern cost and mass.")
    ap.add_argument("--boundary-pattern-runtime-top", type=int, default=10,
                    help="How many active multiplier patterns to evaluate in --boundary-pattern-runtime-report.")
    ap.add_argument("--boundary-pattern-runtime-top-g", type=int, default=8,
                    help="How many costly G-values to print inside each pattern in --boundary-pattern-runtime-report.")
    ap.add_argument("--boundary-pattern-runtime-scope", choices=("active", "full"), default="active",
                    help="Support scope for --boundary-pattern-runtime-report. 'active' matches the exact boundary payload path.")
    ap.add_argument("--boundary-family-candidate-report", action="store_true",
                    help="Rank unevaluated boundary multiplier families by signed float, abs float, and an exact-runtime proxy.")
    ap.add_argument("--boundary-family-residual-report", action="store_true",
                    help="Summarize the remaining unevaluated family mass after excluding exact-certified families, without storing full per-pattern float totals.")
    ap.add_argument("--boundary-residual-structure-report", action="store_true",
                    help="Summarize the remaining unevaluated residual by broader signed groups such as numerator, dyadic orbit, and denominator bucket.")
    ap.add_argument("--boundary-residual-other-structure-report", action="store_true",
                    help="Restrict the residual structure analysis to the 'other' numerator bucket and group it by combined orbit/scale signatures.")
    ap.add_argument("--boundary-product-candidate-report", action="store_true",
                    help="Group unevaluated boundary families by product m*n and rank the grouped residual classes by signed/abs float mass and runtime proxy.")
    ap.add_argument("--exclude-families", nargs="*", default=[],
                    help="Patterns to exclude from --boundary-family-candidate-report, written as m:n.")
    ap.add_argument("--exclude-products", nargs="*", type=int, default=[],
                    help="Product classes m*n to exclude from boundary family/product residual and ranking reports.")
    ap.add_argument("--boundary-family-candidate-top", type=int, default=30,
                    help="How many unevaluated families to print in --boundary-family-candidate-report.")
    ap.add_argument("--boundary-family-candidate-patterns", type=int, default=0,
                    help="How many unevaluated patterns to float-evaluate after proxy ranking in --boundary-family-candidate-report (0 = use max(top*10, top)).")
    ap.add_argument("--boundary-residual-structure-top", type=int, default=20,
                    help="How many top groups to print per table in --boundary-residual-structure-report.")
    ap.add_argument("--boundary-residual-denominator-bucket", type=int, default=20,
                    help="Bucket width for denominator n in --boundary-residual-structure-report.")
    ap.add_argument("--boundary-pattern-family-exact-topn", type=int, default=0,
                    help="Evaluate the top N unevaluated families exactly after ranking them by the chosen float criterion.")
    ap.add_argument("--boundary-pattern-family-topn-order", choices=("negative", "positive", "abs", "runtime"), default="negative",
                    help="Ranking used by --boundary-pattern-family-exact-topn.")
    ap.add_argument("--boundary-pattern-product-exact-topn", type=int, default=0,
                    help="Evaluate the top N unevaluated product classes exactly after ranking them by the chosen float criterion.")
    ap.add_argument("--boundary-pattern-product-topn-order", choices=("negative", "positive", "abs", "runtime"), default="abs",
                    help="Ranking used by --boundary-pattern-product-exact-topn.")
    ap.add_argument("--boundary-pattern-product-exact-batch", nargs="*", type=int, default=[],
                    help="Evaluate the listed product classes exactly as one batch.")
    ap.add_argument("--boundary-skeleton-report", action="store_true",
                    help="Report repeated active boundary block signatures to estimate pattern/skeleton compression potential.")
    ap.add_argument("--boundary-skeleton-top", type=int, default=30,
                    help="How many top repeated keys to print per family in --boundary-skeleton-report.")
    ap.add_argument("--boundary-signed-split-report", action="store_true",
                    help="Compute the full active-scope signed selected/coh2/incoh split and compare it against the full surrogate boundary via an inactive correction term.")
    ap.add_argument("--boundary-signed-split-fast", action="store_true",
                    help="Fast path for active-scope signed split evaluation and chunk export. Skips unrelated full boundary pipeline work.")
    ap.add_argument("--boundary-signed-split-exact", action="store_true",
                    help="Exact path for active-scope signed split evaluation and chunk export.")
    ap.add_argument("--boundary-signed-split-exact-parallel", action="store_true",
                    help="Run exact active-scope chunk emission in parallel after one parent-side setup using forked workers.")
    ap.add_argument("--periodic-main-exact-parallel", action="store_true",
                    help="Run exact periodic-main chunk emission in parallel after one parent-side setup using forked workers.")
    ap.add_argument("--workers", type=int, default=1,
                    help="Worker count for forked exact parallel modes.")
    ap.add_argument("--batch-size", type=int, default=0,
                    help="With --boundary-signed-split-exact and --block-range, emit consecutive exact chunks of this size in one process.")
    ap.add_argument("--checkpoint-dir", type=str, default="",
                    help="Directory for batched exact boundary chunk JSON output.")
    ap.add_argument("--skip-existing-chunks", action="store_true",
                    help="With batched exact boundary chunk emission, skip writing chunks whose JSON already exists.")
    ap.add_argument("--block-range", nargs=2, type=int, metavar=("START", "END"),
                    help="Evaluate only active reversible blocks in the half-open index range [START, END). Intended for chunked boundary-signed-split runs.")
    ap.add_argument("--combine-boundary-chunks", nargs="*", default=[],
                    help="Combine chunk JSON files emitted by --boundary-signed-split-fast or --boundary-signed-split-report --block-range.")
    ap.add_argument("--combine-periodic-main-chunks", nargs="*", default=[],
                    help="Combine exact chunk JSON files emitted by --periodic-main-exact-parallel.")
    ap.add_argument("--emit-periodic-main-ordered-records-json", type=str, default="",
                    help="With --combine-periodic-main-chunks, write one ordered nonzero-record JSON payload for Lean sparse-certificate generation.")
    ap.add_argument("--emit-periodic-main-pair-primitive-lean", nargs=2, type=int, metavar=("Q", "Q2"),
                    help="Emit a Lean primitive-count proof skeleton for one ordered periodic-main pair.")
    ap.add_argument("--emit-periodic-main-pair-records-lean-json", type=str, default="",
                    help="Emit Lean primitive-count proof skeletons for a slice of ordered periodic-main JSON records.")
    ap.add_argument("--emit-periodic-main-pair-records-lean-files", nargs=4,
                    metavar=("JSON", "OUT_DIR", "FILE_PREFIX", "LABEL_PREFIX"),
                    help="Write numbered Lean primitive-count proof modules for filtered ordered periodic-main JSON records.")
    ap.add_argument("--emit-periodic-main-pair-records-split-lean-files", nargs=4,
                    metavar=("JSON", "OUT_DIR", "FILE_PREFIX", "LABEL_PREFIX"),
                    help="Write numbered split Lean proof modules for filtered ordered periodic-main JSON records.")
    ap.add_argument("--emit-periodic-main-zero-records-json", nargs=2, metavar=("NONZERO_JSON", "OUT_JSON"),
                    help="Write ordered full-block zero records by subtracting ordered nonzero records from the full-block support.")
    ap.add_argument("--periodic-main-zero-classification-report", type=str, default="",
                    help="Print a classification report for ordered periodic-main zero-record JSON.")
    ap.add_argument("--periodic-main-dyadic-zero-mechanism-report", type=str, default="",
                    help="Print a structural mechanism report for dyadic-exception ordered zero-record JSON.")
    ap.add_argument("--periodic-main-zero-report-exclude-left", nargs="*", type=int, default=[],
                    help="Left q rows to exclude from --periodic-main-zero-classification-report.")
    ap.add_argument("--periodic-main-zero-report-nonzero-json", type=str, default="",
                    help="Optional ordered nonzero-record JSON used to detect zero rows with a single dyadic exception.")
    ap.add_argument("--periodic-main-zero-report-top", type=int, default=40,
                    help="Number of top rows/classes to print in --periodic-main-zero-classification-report.")
    ap.add_argument("--emit-periodic-main-dyadic-exception-zero-records-json", nargs=3,
                    metavar=("ZERO_JSON", "NONZERO_JSON", "OUT_JSON"),
                    help="Write the zero records whose left row has exactly one nonzero dyadic partner.")
    ap.add_argument("--periodic-main-dyadic-exception-symmetric", action="store_true",
                    help="With --emit-periodic-main-dyadic-exception-zero-records-json, include records whose right side is also a dyadic-exception row.")
    ap.add_argument("--emit-periodic-main-unit-two-zero-records-json", nargs=2,
                    metavar=("ZERO_JSON", "OUT_JSON"),
                    help="Write zero records with left side 1 or 2; use --periodic-main-unit-two-symmetric to include right side 1 or 2.")
    ap.add_argument("--periodic-main-unit-two-symmetric", action="store_true",
                    help="With --emit-periodic-main-unit-two-zero-records-json, include records whose right side is 1 or 2.")
    ap.add_argument("--emit-periodic-main-residual-zero-records-json", nargs="+", default=[],
                    metavar=("ZERO_JSON", "REMOVE_JSON... OUT_JSON"),
                    help="Write zero records after excluding left rows and subtracting one or more zero-record payloads.")
    ap.add_argument("--emit-periodic-main-coverage-lean", nargs=2, metavar=("NONZERO_JSON", "ZERO_JSON"),
                    help="Emit Lean facts that ordered nonzero and zero records exactly cover the full periodic-main block support.")
    ap.add_argument("--emit-periodic-main-nonzero-coverage-lean", type=str, default="",
                    help="Emit Lean coverage/cardinality facts for ordered nonzero periodic-main records.")
    ap.add_argument("--emit-periodic-main-zero-coverage-lean", type=str, default="",
                    help="Emit Lean coverage/cardinality facts for ordered zero periodic-main records.")
    ap.add_argument("--emit-periodic-main-coverage-assembly-lean", nargs=2, metavar=("NONZERO_JSON", "ZERO_JSON"),
                    help="Emit Lean assembly facts importing split nonzero/zero periodic-main coverage modules.")
    ap.add_argument("--emit-periodic-main-row-batch-assembly-lean", nargs=2, metavar=("NONZERO_JSON", "ZERO_JSON"),
                    help="Emit a Lean row-slice assembly theorem for the periodic-main certificate from ordered record JSON payloads.")
    ap.add_argument("--emit-periodic-main-row-exact-json", nargs=2, metavar=("ROW", "OUT_JSON"),
                    help="Compute one periodic-main ordered row exactly and write a row-local ordered-record JSON payload.")
    ap.add_argument("--emit-periodic-main-record-set-coverage-chunk-lean", nargs=3, metavar=("JSON", "NAME", "CHUNK_INDEX"),
                    help="Emit one 100-record Lean coverage chunk for a named periodic-main record set.")
    ap.add_argument("--emit-periodic-main-record-set-coverage-chunk-files", nargs=4,
                    metavar=("JSON", "NAME", "OUT_DIR", "FILE_PREFIX"),
                    help="Write every 100-record Lean coverage chunk file for a named periodic-main record set.")
    ap.add_argument("--emit-periodic-main-record-set-coverage-chunk-assembly-lean", nargs=3,
                    metavar=("JSON", "NAME", "MODULE_PREFIX"),
                    help="Emit Lean assembly facts importing chunk modules for a named periodic-main record set.")
    ap.add_argument("--emit-periodic-main-record-set-coverage-group-files", nargs=5,
                    metavar=("JSON", "NAME", "OUT_DIR", "FILE_PREFIX", "CHUNK_MODULE_PREFIX"),
                    help="Write grouped Lean coverage assembly files over chunk modules for a named periodic-main record set.")
    ap.add_argument("--emit-periodic-main-record-set-coverage-grouped-assembly-lean", nargs=3,
                    metavar=("JSON", "NAME", "GROUP_MODULE_PREFIX"),
                    help="Emit final Lean coverage assembly facts importing grouped modules for a named periodic-main record set.")
    ap.add_argument("--emit-periodic-main-zero-value-chunk-assembly-lean", nargs=6,
                    metavar=("TARGET_SET", "ASSEMBLY_SET", "THEOREM", "MODULE_PREFIX", "LABEL_PREFIX", "CHUNK_COUNT"),
                    help="Emit a value-on-record theorem for a target zero-record set from generated zero-record chunk modules.")
    ap.add_argument("--emit-periodic-main-zero-value-chunk-group-lean", nargs=6,
                    metavar=("GROUP_SET", "THEOREM", "MODULE_PREFIX", "LABEL_PREFIX", "START_INDEX", "CHUNK_COUNT"),
                    help="Emit a group theorem over a consecutive range of generated zero-record chunk modules.")
    ap.add_argument("--emit-periodic-main-zero-value-grouped-final-lean", nargs=7,
                    metavar=("TARGET_SET", "ASSEMBLY_SET", "THEOREM", "GROUP_MODULE_PREFIX", "GROUP_SET_PREFIX", "GROUP_THEOREM_PREFIX", "GROUP_COUNT"),
                    help="Emit a final zero-record theorem from generated group assembly modules.")
    ap.add_argument("--emit-periodic-main-nonzero-value-chunk-group-lean", nargs=7,
                    metavar=("GROUP_SET", "GROUP_TOTAL", "THEOREM", "MODULE_PREFIX", "LABEL_PREFIX", "START_INDEX", "CHUNK_COUNT"),
                    help="Emit a grouped actual-sum theorem over consecutive generated nonzero-record chunk modules.")
    ap.add_argument("--emit-periodic-main-nonzero-value-grouped-final-lean", nargs=8,
                    metavar=("TARGET_SET", "ASSEMBLY_SET", "ASSEMBLY_TOTAL", "THEOREM", "GROUP_MODULE_PREFIX", "GROUP_SET_PREFIX", "GROUP_TOTAL_PREFIX", "GROUP_THEOREM_PREFIX"),
                    help="Emit final actual-sum theorem from generated nonzero value group modules.")
    ap.add_argument("--periodic-main-nonzero-value-group-count", type=int, default=0,
                    help="Group count for --emit-periodic-main-nonzero-value-grouped-final-lean.")
    ap.add_argument("--emit-periodic-main-row-value-chunk-group-lean", nargs=7,
                    metavar=("GROUP_SET", "GROUP_TOTAL", "THEOREM", "MODULE_PREFIX", "LABEL_PREFIX", "START_INDEX", "CHUNK_COUNT"),
                    help="Emit a row-local grouped actual-sum theorem over generated record modules.")
    ap.add_argument("--emit-periodic-main-row-value-grouped-final-lean", nargs=9,
                    metavar=("TARGET_SET", "TARGET_TOTAL", "ASSEMBLY_SET", "ASSEMBLY_TOTAL", "THEOREM", "GROUP_MODULE_PREFIX", "GROUP_SET_PREFIX", "GROUP_TOTAL_PREFIX", "GROUP_THEOREM_PREFIX"),
                    help="Emit a row-local final actual-sum theorem from grouped record modules.")
    ap.add_argument("--periodic-main-row-value-group-count", type=int, default=0,
                    help="Group count for --emit-periodic-main-row-value-grouped-final-lean.")
    ap.add_argument("--periodic-main-row-record-complexity-report", type=str, default="",
                    help="Print a complexity report for a row-local periodic-main exact-record JSON payload.")
    ap.add_argument("--periodic-main-row-record-complexity-top", type=int, default=30,
                    help="Number of top records/groups to show in --periodic-main-row-record-complexity-report.")
    ap.add_argument("--periodic-main-row-record-complexity-group-size", type=int, default=50,
                    help="Group size used when aggregating row-record complexity.")
    ap.add_argument("--periodic-main-row-record-complexity-completed-records", type=int, default=0,
                    help="Record checkpoint used to distinguish pending records in the row-record complexity report.")
    ap.add_argument("--periodic-main-row-record-complexity-json-out", type=str, default="",
                    help="Optional JSON output path for --periodic-main-row-record-complexity-report.")
    ap.add_argument("--periodic-main-coverage-chunk-size", type=int, default=100,
                    help="Record count per periodic-main coverage chunk module.")
    ap.add_argument("--periodic-main-coverage-group-chunks", type=int, default=25,
                    help="Chunk modules per periodic-main coverage group module.")
    ap.add_argument("--periodic-main-row-batch-size", type=int, default=500,
                    help="Row width for --emit-periodic-main-row-batch-assembly-lean.")
    ap.add_argument("--periodic-main-row-plan", choices=("fixed", "density"), default="fixed",
                    help="Row partition plan for --emit-periodic-main-row-batch-assembly-lean.")
    ap.add_argument("--periodic-main-row-target-pairs", type=int, default=1500,
                    help="Target support-pair count per density-aware periodic-main row slice.")
    ap.add_argument("--periodic-main-row-single-threshold", type=int, default=1000,
                    help="Emit a single-row slice when a row has at least this many support pairs.")
    ap.add_argument("--periodic-main-row-max-width", type=int, default=500,
                    help="Maximum row width for density-aware periodic-main row slices.")
    ap.add_argument("--periodic-main-record-start", type=int, default=0,
                    help="Starting record index for --emit-periodic-main-pair-records-lean-json.")
    ap.add_argument("--periodic-main-record-count", type=int, default=0,
                    help="Number of records to emit for --emit-periodic-main-pair-records-lean-json; 0 means all remaining.")
    ap.add_argument("--periodic-main-record-filter-left", nargs="*", type=int, default=[],
                    help="With --emit-periodic-main-pair-records-lean-json, keep only records with q in this left-row list.")
    ap.add_argument("--periodic-main-record-filter-right", nargs="*", type=int, default=[],
                    help="With --emit-periodic-main-pair-records-lean-json, keep only records with q' in this right-column list.")
    ap.add_argument("--periodic-main-record-filter-gcd", nargs="*", type=int, default=[],
                    help="With --emit-periodic-main-pair-records-lean-json, keep only records with gcd(q,q') in this list.")
    ap.add_argument("--periodic-main-record-filter-left-div3",
                    choices=("any", "yes", "no"), default="any",
                    help="With --emit-periodic-main-pair-records-lean-json, filter by whether 3 divides q.")
    ap.add_argument("--periodic-main-record-filter-right-div3",
                    choices=("any", "yes", "no"), default="any",
                    help="With --emit-periodic-main-pair-records-lean-json, filter by whether 3 divides q'.")
    ap.add_argument("--periodic-main-record-filter-coprime",
                    choices=("any", "coprime", "noncoprime"), default="any",
                    help="With --emit-periodic-main-pair-records-lean-json, filter by gcd(q,q2).")
    ap.add_argument("--periodic-main-record-filter-exclude-unit-two", action="store_true",
                    help="With --emit-periodic-main-pair-records-lean-json, drop records with q or q2 equal to 1 or 2.")
    ap.add_argument("--periodic-main-record-batch-label", type=str, default="Batch000",
                    help="Stable Lean-name label for --emit-periodic-main-pair-records-lean-json output.")
    ap.add_argument("--periodic-main-record-file-chunk-size", type=int, default=1,
                    help="Record count per module for --emit-periodic-main-pair-records-lean-files.")
    ap.add_argument("--periodic-main-record-file-skip-existing", action="store_true",
                    help="With --emit-periodic-main-pair-records-lean-files, skip files that already exist.")
    ap.add_argument("--periodic-main-record-force-top-level-helpers", action="store_true",
                    help="With --emit-periodic-main-pair-records-lean-files, emit divisor/count/term helpers as top-level theorems even for small records.")
    ap.add_argument("--periodic-main-split-row-part-size", type=int, default=8,
                    help="Right-divisor count per row-part helper module for split periodic-main pair records.")
    ap.add_argument("--periodic-main-split-inline-row-parts", action="store_true",
                    help="Inline term arithmetic into row-part modules instead of emitting one helper module per term.")
    ap.add_argument("--periodic-main-disable-q42-cancel", action="store_true",
                    help="With --emit-periodic-main-pair-records-split-lean-files, use the ordinary split emitter for q=42 zero records instead of the specialized q=42 cancellation emitter.")
    ap.add_argument("--periodic-main-assembly-extra-imports", nargs="*", default=[],
                    help="Extra Lean module imports for --emit-periodic-main-zero-value-chunk-assembly-lean.")
    ap.add_argument("--periodic-main-group-set-suffix", type=str, default="Pairs",
                    help="Suffix appended after each zero-value group set index in --emit-periodic-main-zero-value-grouped-final-lean.")
    ap.add_argument("--periodic-main-group-theorem-suffix", type=str, default="_value_on_records",
                    help="Suffix appended after each zero-value group theorem index in --emit-periodic-main-zero-value-grouped-final-lean.")
    ap.add_argument("--emit-boundary-final-certificate", action="store_true",
                    help="With --combine-boundary-chunks, emit Lean-facing ℚ certificate defs for active signed total, inactive correction, and full boundary.")
    ap.add_argument("--boundary-full-signed-decimal", type=str, default="",
                    help="With --emit-boundary-final-certificate, the full surrogate boundary signed decimal to package as the final full certificate value.")
    args = ap.parse_args()

    if args.periodic_main_row_record_complexity_report:
        periodic_main_row_record_complexity_report(
            payload_path=args.periodic_main_row_record_complexity_report,
            top=args.periodic_main_row_record_complexity_top,
            group_size=args.periodic_main_row_record_complexity_group_size,
            completed_records=args.periodic_main_row_record_complexity_completed_records,
            json_out=args.periodic_main_row_record_complexity_json_out,
        )
        return

    if args.periodic_main_dyadic_zero_mechanism_report:
        with open(args.periodic_main_dyadic_zero_mechanism_report, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") != "periodic-main-ordered-zero-records":
            raise SystemExit(
                f"{args.periodic_main_dyadic_zero_mechanism_report}: not a periodic-main ordered zero-record payload"
            )
        periodic_main_dyadic_zero_mechanism_report(
            records=list(payload.get("records", [])),
            top=args.periodic_main_zero_report_top,
        )
        return

    if args.periodic_main_zero_classification_report:
        with open(args.periodic_main_zero_classification_report, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") != "periodic-main-ordered-zero-records":
            raise SystemExit(
                f"{args.periodic_main_zero_classification_report}: not a periodic-main ordered zero-record payload"
            )
        nonzero_records = None
        if args.periodic_main_zero_report_nonzero_json:
            with open(args.periodic_main_zero_report_nonzero_json, "r", encoding="utf-8") as fh:
                nonzero_payload = json.load(fh)
            if nonzero_payload.get("mode") != "periodic-main-ordered-nonzero-records":
                raise SystemExit(
                    f"{args.periodic_main_zero_report_nonzero_json}: not a periodic-main ordered nonzero-record payload"
                )
            nonzero_records = list(nonzero_payload.get("records", []))
        periodic_main_zero_classification_report(
            records=list(payload.get("records", [])),
            nonzero_records=nonzero_records,
            exclude_left=set(args.periodic_main_zero_report_exclude_left),
            top=args.periodic_main_zero_report_top,
        )
        return

    if args.emit_periodic_main_dyadic_exception_zero_records_json:
        zero_path, nonzero_path, out_path = args.emit_periodic_main_dyadic_exception_zero_records_json
        with open(zero_path, "r", encoding="utf-8") as fh:
            zero_payload = json.load(fh)
        if zero_payload.get("mode") != "periodic-main-ordered-zero-records":
            raise SystemExit(f"{zero_path}: not a periodic-main ordered zero-record payload")
        with open(nonzero_path, "r", encoding="utf-8") as fh:
            nonzero_payload = json.load(fh)
        if nonzero_payload.get("mode") != "periodic-main-ordered-nonzero-records":
            raise SystemExit(f"{nonzero_path}: not a periodic-main ordered nonzero-record payload")
        payload = emit_periodic_main_dyadic_exception_zero_records_json(
            zero_payload=zero_payload,
            nonzero_payload=nonzero_payload,
            exclude_left=set(args.periodic_main_zero_report_exclude_left),
            symmetric=args.periodic_main_dyadic_exception_symmetric,
        )
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, sort_keys=True)
            fh.write("\n")
        print(
            f"wrote {payload['record_count']} dyadic-exception zero records "
            f"across {payload['row_count']} rows to {out_path}"
        )
        return

    if args.emit_periodic_main_unit_two_zero_records_json:
        zero_path, out_path = args.emit_periodic_main_unit_two_zero_records_json
        with open(zero_path, "r", encoding="utf-8") as fh:
            zero_payload = json.load(fh)
        if zero_payload.get("mode") != "periodic-main-ordered-zero-records":
            raise SystemExit(f"{zero_path}: not a periodic-main ordered zero-record payload")
        payload = emit_periodic_main_unit_two_zero_records_json(
            zero_payload=zero_payload,
            symmetric=args.periodic_main_unit_two_symmetric,
        )
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, sort_keys=True)
            fh.write("\n")
        print(
            f"wrote {payload['record_count']} unit/two zero records "
            f"across {payload['row_count']} rows to {out_path}"
        )
        return

    if args.emit_periodic_main_residual_zero_records_json:
        residual_args = args.emit_periodic_main_residual_zero_records_json
        if len(residual_args) < 3:
            raise SystemExit(
                "--emit-periodic-main-residual-zero-records-json requires ZERO_JSON REMOVE_JSON... OUT_JSON"
            )
        zero_path = residual_args[0]
        remove_paths = residual_args[1:-1]
        out_path = residual_args[-1]
        with open(zero_path, "r", encoding="utf-8") as fh:
            zero_payload = json.load(fh)
        if zero_payload.get("mode") != "periodic-main-ordered-zero-records":
            raise SystemExit(f"{zero_path}: not a periodic-main ordered zero-record payload")
        remove_payloads = []
        for remove_path in remove_paths:
            with open(remove_path, "r", encoding="utf-8") as fh:
                remove_payload = json.load(fh)
            if remove_payload.get("mode") != "periodic-main-ordered-zero-records":
                raise SystemExit(f"{remove_path}: not a periodic-main ordered zero-record payload")
            remove_payloads.append(remove_payload)
        payload = emit_periodic_main_residual_zero_records_json(
            zero_payload=zero_payload,
            remove_payloads=remove_payloads,
            exclude_left=set(args.periodic_main_zero_report_exclude_left),
        )
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, sort_keys=True)
            fh.write("\n")
        print(
            f"wrote {payload['record_count']} residual zero records "
            f"across {payload['row_count']} rows to {out_path}"
        )
        return

    if args.emit_periodic_main_record_set_coverage_chunk_files:
        payload_path, name, out_dir, file_prefix = args.emit_periodic_main_record_set_coverage_chunk_files
        with open(payload_path, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") not in {
            "periodic-main-ordered-nonzero-records",
            "periodic-main-ordered-zero-records",
        }:
            raise SystemExit(f"{payload_path}: not a periodic-main ordered-record payload")
        emit_periodic_main_record_set_coverage_chunk_files(
            name=name,
            records=list(payload.get("records", [])),
            out_dir=out_dir,
            file_prefix=file_prefix,
            chunk_size=args.periodic_main_coverage_chunk_size,
            skip_existing=args.skip_existing_chunks,
        )
        return

    if args.emit_periodic_main_row_batch_assembly_lean:
        nonzero_path, zero_path = args.emit_periodic_main_row_batch_assembly_lean
        nonzero_payload = load_periodic_main_ordered_record_payload(
            nonzero_path,
            expected_mode="periodic-main-ordered-nonzero-records",
        )
        zero_payload = load_periodic_main_ordered_record_payload(
            zero_path,
            expected_mode="periodic-main-ordered-zero-records",
        )
        emit_periodic_main_row_batch_assembly_lean(
            nonzero_records=list(nonzero_payload.get("records", [])),
            zero_records=list(zero_payload.get("records", [])),
            row_batch_size=args.periodic_main_row_batch_size,
            row_plan=args.periodic_main_row_plan,
            target_pairs=args.periodic_main_row_target_pairs,
            single_threshold=args.periodic_main_row_single_threshold,
            max_width=args.periodic_main_row_max_width,
        )
        return

    if args.emit_periodic_main_record_set_coverage_chunk_assembly_lean:
        payload_path, name, module_prefix = args.emit_periodic_main_record_set_coverage_chunk_assembly_lean
        with open(payload_path, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") not in {
            "periodic-main-ordered-nonzero-records",
            "periodic-main-ordered-zero-records",
        }:
            raise SystemExit(f"{payload_path}: not a periodic-main ordered-record payload")
        emit_periodic_main_record_set_coverage_chunk_assembly_lean(
            name=name,
            record_count=len(list(payload.get("records", []))),
            module_prefix=module_prefix,
            chunk_size=args.periodic_main_coverage_chunk_size,
        )
        return

    if args.emit_periodic_main_record_set_coverage_group_files:
        payload_path, name, out_dir, file_prefix, chunk_module_prefix = args.emit_periodic_main_record_set_coverage_group_files
        with open(payload_path, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") not in {
            "periodic-main-ordered-nonzero-records",
            "periodic-main-ordered-zero-records",
        }:
            raise SystemExit(f"{payload_path}: not a periodic-main ordered-record payload")
        emit_periodic_main_record_set_coverage_group_files(
            name=name,
            records=list(payload.get("records", [])),
            out_dir=out_dir,
            file_prefix=file_prefix,
            chunk_module_prefix=chunk_module_prefix,
            chunk_size=args.periodic_main_coverage_chunk_size,
            group_chunk_size=args.periodic_main_coverage_group_chunks,
            skip_existing=args.skip_existing_chunks,
        )
        return

    if args.emit_periodic_main_record_set_coverage_grouped_assembly_lean:
        payload_path, name, group_module_prefix = args.emit_periodic_main_record_set_coverage_grouped_assembly_lean
        with open(payload_path, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") not in {
            "periodic-main-ordered-nonzero-records",
            "periodic-main-ordered-zero-records",
        }:
            raise SystemExit(f"{payload_path}: not a periodic-main ordered-record payload")
        emit_periodic_main_record_set_coverage_grouped_assembly_lean(
            name=name,
            records=list(payload.get("records", [])),
            group_module_prefix=group_module_prefix,
            chunk_size=args.periodic_main_coverage_chunk_size,
            group_chunk_size=args.periodic_main_coverage_group_chunks,
        )
        return

    if args.emit_periodic_main_zero_value_chunk_assembly_lean:
        target_set_name, assembly_set_name, theorem_name, module_prefix, label_prefix, chunk_count_raw = (
            args.emit_periodic_main_zero_value_chunk_assembly_lean
        )
        emit_periodic_main_zero_value_chunk_assembly_lean(
            target_set_name=target_set_name,
            assembly_set_name=assembly_set_name,
            theorem_name=theorem_name,
            module_prefix=module_prefix,
            label_prefix=label_prefix,
            chunk_count=int(chunk_count_raw),
            extra_imports=list(args.periodic_main_assembly_extra_imports),
        )
        return

    if args.emit_periodic_main_zero_value_chunk_group_lean:
        group_set_name, theorem_name, module_prefix, label_prefix, start_index_raw, chunk_count_raw = (
            args.emit_periodic_main_zero_value_chunk_group_lean
        )
        emit_periodic_main_zero_value_chunk_group_lean(
            group_set_name=group_set_name,
            theorem_name=theorem_name,
            module_prefix=module_prefix,
            label_prefix=label_prefix,
            start_index=int(start_index_raw),
            chunk_count=int(chunk_count_raw),
            extra_imports=list(args.periodic_main_assembly_extra_imports),
        )
        return

    if args.emit_periodic_main_zero_value_grouped_final_lean:
        (
            target_set_name,
            assembly_set_name,
            theorem_name,
            group_module_prefix,
            group_set_prefix,
            group_theorem_prefix,
            group_count_raw,
        ) = args.emit_periodic_main_zero_value_grouped_final_lean
        emit_periodic_main_zero_value_grouped_final_lean(
            target_set_name=target_set_name,
            assembly_set_name=assembly_set_name,
            theorem_name=theorem_name,
            group_module_prefix=group_module_prefix,
            group_set_prefix=group_set_prefix,
            group_set_suffix=args.periodic_main_group_set_suffix,
            group_theorem_prefix=group_theorem_prefix,
            group_theorem_suffix=args.periodic_main_group_theorem_suffix,
            group_count=int(group_count_raw),
            extra_imports=list(args.periodic_main_assembly_extra_imports),
        )
        return

    if args.emit_periodic_main_nonzero_value_chunk_group_lean:
        (
            group_set_name,
            group_total_name,
            theorem_name,
            module_prefix,
            label_prefix,
            start_index_raw,
            chunk_count_raw,
        ) = args.emit_periodic_main_nonzero_value_chunk_group_lean
        emit_periodic_main_nonzero_value_chunk_group_lean(
            group_set_name=group_set_name,
            group_total_name=group_total_name,
            theorem_name=theorem_name,
            module_prefix=module_prefix,
            label_prefix=label_prefix,
            start_index=int(start_index_raw),
            chunk_count=int(chunk_count_raw),
            extra_imports=list(args.periodic_main_assembly_extra_imports),
        )
        return

    if args.emit_periodic_main_nonzero_value_grouped_final_lean:
        (
            target_set_name,
            assembly_set_name,
            assembly_total_name,
            theorem_name,
            group_module_prefix,
            group_set_prefix,
            group_total_prefix,
            group_theorem_prefix,
        ) = args.emit_periodic_main_nonzero_value_grouped_final_lean
        if args.periodic_main_nonzero_value_group_count <= 0:
            raise SystemExit(
                "--emit-periodic-main-nonzero-value-grouped-final-lean requires "
                "--periodic-main-nonzero-value-group-count N"
            )
        emit_periodic_main_nonzero_value_grouped_final_lean(
            target_set_name=target_set_name,
            assembly_set_name=assembly_set_name,
            assembly_total_name=assembly_total_name,
            theorem_name=theorem_name,
            group_module_prefix=group_module_prefix,
            group_set_prefix=group_set_prefix,
            group_total_prefix=group_total_prefix,
            group_theorem_prefix=group_theorem_prefix,
            group_count=args.periodic_main_nonzero_value_group_count,
            extra_imports=list(args.periodic_main_assembly_extra_imports),
        )
        return

    if args.emit_periodic_main_row_value_chunk_group_lean:
        (
            group_set_name,
            group_total_name,
            theorem_name,
            module_prefix,
            label_prefix,
            start_index_raw,
            chunk_count_raw,
        ) = args.emit_periodic_main_row_value_chunk_group_lean
        emit_periodic_main_row_value_chunk_group_lean(
            group_set_name=group_set_name,
            group_total_name=group_total_name,
            theorem_name=theorem_name,
            module_prefix=module_prefix,
            label_prefix=label_prefix,
            start_index=int(start_index_raw),
            chunk_count=int(chunk_count_raw),
            extra_imports=list(args.periodic_main_assembly_extra_imports),
        )
        return

    if args.emit_periodic_main_row_value_grouped_final_lean:
        (
            target_set_name,
            target_total_name,
            assembly_set_name,
            assembly_total_name,
            theorem_name,
            group_module_prefix,
            group_set_prefix,
            group_total_prefix,
            group_theorem_prefix,
        ) = args.emit_periodic_main_row_value_grouped_final_lean
        if args.periodic_main_row_value_group_count <= 0:
            raise SystemExit(
                "--emit-periodic-main-row-value-grouped-final-lean requires "
                "--periodic-main-row-value-group-count N"
            )
        emit_periodic_main_row_value_grouped_final_lean(
            target_set_name=target_set_name,
            target_total_name=target_total_name,
            assembly_set_name=assembly_set_name,
            assembly_total_name=assembly_total_name,
            theorem_name=theorem_name,
            group_module_prefix=group_module_prefix,
            group_set_prefix=group_set_prefix,
            group_total_prefix=group_total_prefix,
            group_theorem_prefix=group_theorem_prefix,
            group_count=args.periodic_main_row_value_group_count,
            extra_imports=list(args.periodic_main_assembly_extra_imports),
        )
        return

    if args.emit_periodic_main_record_set_coverage_chunk_lean:
        payload_path, name, chunk_idx_raw = args.emit_periodic_main_record_set_coverage_chunk_lean
        with open(payload_path, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") not in {
            "periodic-main-ordered-nonzero-records",
            "periodic-main-ordered-zero-records",
        }:
            raise SystemExit(f"{payload_path}: not a periodic-main ordered-record payload")
        emit_periodic_main_record_set_coverage_chunk_lean(
            name=name,
            records=list(payload.get("records", [])),
            chunk_idx=int(chunk_idx_raw),
            chunk_size=args.periodic_main_coverage_chunk_size,
        )
        return

    if args.emit_periodic_main_nonzero_coverage_lean:
        with open(args.emit_periodic_main_nonzero_coverage_lean, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") != "periodic-main-ordered-nonzero-records":
            raise SystemExit(
                f"{args.emit_periodic_main_nonzero_coverage_lean}: not a periodic-main ordered nonzero-record payload"
            )
        emit_periodic_main_record_set_coverage_lean(
            name="PeriodicMainNonzeroRecordPairs",
            records=list(payload.get("records", [])),
        )
        return

    if args.emit_periodic_main_zero_coverage_lean:
        with open(args.emit_periodic_main_zero_coverage_lean, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") != "periodic-main-ordered-zero-records":
            raise SystemExit(
                f"{args.emit_periodic_main_zero_coverage_lean}: not a periodic-main ordered zero-record payload"
            )
        emit_periodic_main_record_set_coverage_lean(
            name="PeriodicMainZeroRecordPairs",
            records=list(payload.get("records", [])),
        )
        return

    if args.emit_periodic_main_coverage_assembly_lean:
        nonzero_path, zero_path = args.emit_periodic_main_coverage_assembly_lean
        with open(nonzero_path, "r", encoding="utf-8") as fh:
            nonzero_payload = json.load(fh)
        with open(zero_path, "r", encoding="utf-8") as fh:
            zero_payload = json.load(fh)
        if nonzero_payload.get("mode") != "periodic-main-ordered-nonzero-records":
            raise SystemExit(f"{nonzero_path}: not a periodic-main ordered nonzero-record payload")
        if zero_payload.get("mode") != "periodic-main-ordered-zero-records":
            raise SystemExit(f"{zero_path}: not a periodic-main ordered zero-record payload")
        emit_periodic_main_coverage_assembly_lean(
            nonzero_count=len(list(nonzero_payload.get("records", []))),
            zero_count=len(list(zero_payload.get("records", []))),
        )
        return

    if args.emit_periodic_main_coverage_lean:
        nonzero_path, zero_path = args.emit_periodic_main_coverage_lean
        with open(nonzero_path, "r", encoding="utf-8") as fh:
            nonzero_payload = json.load(fh)
        with open(zero_path, "r", encoding="utf-8") as fh:
            zero_payload = json.load(fh)
        if nonzero_payload.get("mode") != "periodic-main-ordered-nonzero-records":
            raise SystemExit(f"{nonzero_path}: not a periodic-main ordered nonzero-record payload")
        if zero_payload.get("mode") != "periodic-main-ordered-zero-records":
            raise SystemExit(f"{zero_path}: not a periodic-main ordered zero-record payload")
        if int(nonzero_payload.get("X", args.X)) != args.X:
            raise SystemExit(f"{nonzero_path}: payload X={nonzero_payload.get('X')} does not match --X {args.X}")
        if int(zero_payload.get("X", args.X)) != args.X:
            raise SystemExit(f"{zero_path}: payload X={zero_payload.get('X')} does not match --X {args.X}")
        emit_periodic_main_coverage_lean(
            nonzero_records=list(nonzero_payload.get("records", [])),
            zero_records=list(zero_payload.get("records", [])),
        )
        return

    if args.emit_periodic_main_pair_records_split_lean_files:
        if args.true_series:
            raise SystemExit("--emit-periodic-main-pair-records-split-lean-files is only implemented for the surrogate normalization")
        payload_path, out_dir, file_prefix, label_prefix = args.emit_periodic_main_pair_records_split_lean_files
        X = args.X
        record_start = max(0, args.periodic_main_record_start)
        record_count = max(0, args.periodic_main_record_count)
        with open(payload_path, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") not in {
            "periodic-main-ordered-nonzero-records",
            "periodic-main-ordered-zero-records",
        }:
            raise SystemExit(f"{payload_path}: not a periodic-main ordered-record payload")
        if int(payload.get("X", X)) != X:
            raise SystemExit(
                f"{payload_path}: payload X={payload.get('X')} does not match --X {X}"
            )
        records_all = filter_periodic_main_records_for_lean(
            list(payload.get("records", [])),
            left_rows=set(args.periodic_main_record_filter_left),
            right_rows=set(args.periodic_main_record_filter_right),
            gcd_values=set(args.periodic_main_record_filter_gcd),
            left_div3_filter=args.periodic_main_record_filter_left_div3,
            right_div3_filter=args.periodic_main_record_filter_right_div3,
            coprime_filter=args.periodic_main_record_filter_coprime,
            exclude_unit_two=args.periodic_main_record_filter_exclude_unit_two,
        )
        if record_start > len(records_all):
            raise SystemExit(
                f"--periodic-main-record-start={record_start} out of range for {len(records_all)} records"
            )
        record_end = len(records_all) if record_count == 0 else min(len(records_all), record_start + record_count)
        records = records_all[record_start:record_end]
        written_count = emit_periodic_main_pair_record_split_lean_files(
            X=X,
            records=records,
            out_dir=out_dir,
            file_prefix=file_prefix,
            label_prefix=label_prefix,
            index_offset=record_start,
            skip_existing=args.periodic_main_record_file_skip_existing,
            row_part_size=args.periodic_main_split_row_part_size,
            inline_row_parts=args.periodic_main_split_inline_row_parts,
            disable_q42_cancel=args.periodic_main_disable_q42_cancel,
        )
        print(
            f"[done] wrote split modules for {written_count} selected records",
            file=sys.stderr,
        )
        return

    if args.emit_periodic_main_pair_records_lean_files:
        if args.true_series:
            raise SystemExit("--emit-periodic-main-pair-records-lean-files is only implemented for the surrogate normalization")
        payload_path, out_dir, file_prefix, label_prefix = args.emit_periodic_main_pair_records_lean_files
        X = args.X
        record_start = max(0, args.periodic_main_record_start)
        record_count = max(0, args.periodic_main_record_count)
        with open(payload_path, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") not in {
            "periodic-main-ordered-nonzero-records",
            "periodic-main-ordered-zero-records",
        }:
            raise SystemExit(f"{payload_path}: not a periodic-main ordered-record payload")
        if int(payload.get("X", X)) != X:
            raise SystemExit(
                f"{payload_path}: payload X={payload.get('X')} does not match --X {X}"
            )
        records_all = filter_periodic_main_records_for_lean(
            list(payload.get("records", [])),
            left_rows=set(args.periodic_main_record_filter_left),
            right_rows=set(args.periodic_main_record_filter_right),
            gcd_values=set(args.periodic_main_record_filter_gcd),
            left_div3_filter=args.periodic_main_record_filter_left_div3,
            right_div3_filter=args.periodic_main_record_filter_right_div3,
            coprime_filter=args.periodic_main_record_filter_coprime,
            exclude_unit_two=args.periodic_main_record_filter_exclude_unit_two,
        )
        if record_start > len(records_all):
            raise SystemExit(
                f"--periodic-main-record-start={record_start} out of range for {len(records_all)} records"
            )
        record_end = len(records_all) if record_count == 0 else min(len(records_all), record_start + record_count)
        records = records_all[record_start:record_end]
        chunk_count = emit_periodic_main_pair_record_lean_chunk_files(
            X=X,
            records=records,
            zero_record_batch=payload.get("mode") == "periodic-main-ordered-zero-records",
            out_dir=out_dir,
            file_prefix=file_prefix,
            label_prefix=label_prefix,
            chunk_size=args.periodic_main_record_file_chunk_size,
            index_offset=record_start,
            skip_existing=args.periodic_main_record_file_skip_existing,
            force_top_level_helpers=args.periodic_main_record_force_top_level_helpers,
        )
        print(
            f"[done] wrote {chunk_count} chunk slots for {len(records)} selected records",
            file=sys.stderr,
        )
        return

    if args.emit_periodic_main_pair_records_lean_json:
        if args.true_series:
            raise SystemExit("--emit-periodic-main-pair-records-lean-json is only implemented for the surrogate normalization")
        X = args.X
        record_start = max(0, args.periodic_main_record_start)
        record_count = max(0, args.periodic_main_record_count)
        with open(args.emit_periodic_main_pair_records_lean_json, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") not in {
            "periodic-main-ordered-nonzero-records",
            "periodic-main-ordered-zero-records",
        }:
            raise SystemExit(
                f"{args.emit_periodic_main_pair_records_lean_json}: not a periodic-main ordered-record payload"
            )
        if int(payload.get("X", X)) != X:
            raise SystemExit(
                f"{args.emit_periodic_main_pair_records_lean_json}: payload X={payload.get('X')} "
                f"does not match --X {X}"
            )
        records_all = filter_periodic_main_records_for_lean(
            list(payload.get("records", [])),
            left_rows=set(args.periodic_main_record_filter_left),
            right_rows=set(args.periodic_main_record_filter_right),
            gcd_values=set(args.periodic_main_record_filter_gcd),
            left_div3_filter=args.periodic_main_record_filter_left_div3,
            right_div3_filter=args.periodic_main_record_filter_right_div3,
            coprime_filter=args.periodic_main_record_filter_coprime,
            exclude_unit_two=args.periodic_main_record_filter_exclude_unit_two,
        )
        if record_start > len(records_all):
            raise SystemExit(
                f"--periodic-main-record-start={record_start} out of range for {len(records_all)} records"
            )
        record_end = len(records_all) if record_count == 0 else min(len(records_all), record_start + record_count)
        records = records_all[record_start:record_end]
        if not records:
            raise SystemExit("selected periodic-main record slice is empty")
        q_support = sorted(
            {int(record["q"]) for record in records}
            | {int(record["q2"]) for record in records}
        )
        mu, phi = mobius_phi_sieve(Q0)
        spf = spf_sieve(Q0)
        even_card = len(even_window_points(X))
        exact_ctx = build_surrogate_boundary_exact_context(X, mu, phi, spf, even_card, q_support)
        emit_periodic_main_pair_primitive_lean_header()
        print(
            f"/- Generated periodic-main ordered-record proofs for selected JSON indices "
            f"[{record_start},{record_end}). -/"
        )
        print()
        for record in records:
            q = int(record["q"])
            q2 = int(record["q2"])
            expected = Fraction(int(record["value_num"]), int(record["value_den"]))
            emit_periodic_main_pair_primitive_lean_theorems(
                X=X,
                q=q,
                q2=q2,
                exact_ctx=exact_ctx,
                expected_summand=expected,
                force_top_level_helpers=args.periodic_main_record_force_top_level_helpers,
            )
        if payload.get("mode") == "periodic-main-ordered-zero-records":
            emit_periodic_main_zero_record_batch_wrapper(
                X=X,
                label=args.periodic_main_record_batch_label,
                records=records,
            )
        else:
            emit_periodic_main_record_batch_wrapper(
                X=X,
                label=args.periodic_main_record_batch_label,
                records=records,
            )
        emit_periodic_main_pair_primitive_lean_footer()
        return

    if args.emit_periodic_main_pair_primitive_lean:
        if args.true_series:
            raise SystemExit("--emit-periodic-main-pair-primitive-lean is only implemented for the surrogate normalization")
        X = args.X
        q, q2 = args.emit_periodic_main_pair_primitive_lean
        if q <= 0 or q2 <= 0:
            raise SystemExit("--emit-periodic-main-pair-primitive-lean expects positive moduli")
        mu, phi = mobius_phi_sieve(Q0)
        spf = spf_sieve(Q0)
        even_card = len(even_window_points(X))
        exact_ctx = build_surrogate_boundary_exact_context(X, mu, phi, spf, even_card, sorted(set([q, q2])))
        divs_q = exact_ctx["divisors_by_q"][q]
        divs_q2 = exact_ctx["divisors_by_q"][q2]
        first_even, even_count = full_block_even_progression(X, block_period(q, q2))
        coeff_q = exact_ctx["coeff_rat"][q]
        coeff_q2 = exact_ctx["coeff_rat"][q2]
        summand_value = centered_ramanujan_pair_periodic_main_term_rat_cached(X, q, q2, exact_ctx)
        if coeff_q == 0 or coeff_q2 == 0:
            centered_term = Fraction(0, 1)
        else:
            centered_term = summand_value / (coeff_q * coeff_q2)
        name = f"periodicMainPair_{q}_{q2}_X{X}"

        def lean_nat_list(values: list[int]) -> str:
            return "[" + ", ".join(str(v) for v in values) + "]"

        def emit_block_periodic_count_proof(
            *,
            theorem_name: str,
            q0: int,
            g0: int,
            expected: int,
        ) -> None:
            print(
                f"  have {theorem_name} : "
                f"rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q0} {g0} = ({expected} : ℚ) := by"
            )
            print("    native_decide")

        def emit_pair_resolved_count_proof(
            *,
            theorem_name: str,
            g: int,
            h: int,
            expected: int,
        ) -> None:
            print(
                f"  have {theorem_name} : "
                f"rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} {g} {h} = ({expected} : ℚ) := by"
            )
            print("    native_decide")

        print("import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain")
        print()
        print("namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")
        print()
        print("open Goldbach")
        print("open Goldbach.BankParams")
        print("open Goldbach.Windows")
        print()
        print(f"theorem {name}_centeredTerm :")
        print(f"    centeredRamanujanPairPeriodicMainTermRat X0 {q} {q2} = {fraction_to_q_literal(centered_term)} := by")
        print(f"  have hDivLeft : Nat.divisors {q} = ({lean_nat_list(divs_q)} : List ℕ).toFinset := by")
        print("    decide")
        print(f"  have hDivRight : Nat.divisors {q2} = ({lean_nat_list(divs_q2)} : List ℕ).toFinset := by")
        print("    decide")
        for g in divs_q:
            v = exact_ctx["gcd_coeff_by_q"][q][g]
            print(f"  have hCoeffLeft_{g} : ramanujanGcdClassCoeffRat {q} {g} = {fraction_to_q_literal(v)} := by")
            print("    native_decide")
        for h in divs_q2:
            v = exact_ctx["gcd_coeff_by_q"][q2][h]
            print(f"  have hCoeffRight_{h} : ramanujanGcdClassCoeffRat {q2} {h} = {fraction_to_q_literal(v)} := by")
            print("    native_decide")
        for g in divs_q:
            v = exact_ctx["avg_by_q"][q][g]
            print(f"  have hAvgLeft_{g} : ramanujanGcdClassWindowAverageRat X0 {q} {g} = {fraction_to_q_literal(v)} := by")
            print("    native_decide")
        for h in divs_q2:
            v = exact_ctx["avg_by_q"][q2][h]
            print(f"  have hAvgRight_{h} : ramanujanGcdClassWindowAverageRat X0 {q2} {h} = {fraction_to_q_literal(v)} := by")
            print("    native_decide")
        for g in divs_q:
            v = gcd_class_count_in_even_progression(q, g, first_even, even_count, exact_ctx)
            emit_block_periodic_count_proof(theorem_name=f"hBlockLeft_{g}", q0=q, g0=g, expected=v)
        for h in divs_q2:
            v = gcd_class_count_in_even_progression(q2, h, first_even, even_count, exact_ctx)
            emit_block_periodic_count_proof(theorem_name=f"hBlockRight_{h}", q0=q2, g0=h, expected=v)
        for g in divs_q:
            for h in divs_q2:
                v = gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, exact_ctx)
                emit_pair_resolved_count_proof(theorem_name=f"hPair_{g}_{h}", g=g, h=h, expected=v)
        full_blocks = (H + 1) // block_period(q, q2)
        even_count_rat = Fraction(even_count, 1)
        print("  let T : ℕ → ℕ → ℚ := fun g h =>")
        print(f"    ramanujanGcdClassCoeffRat {q} g * ramanujanGcdClassCoeffRat {q2} h")
        print(f"      * ((((H + 1) / centeredRamanujanPairBlockPeriod {q} {q2}) : ℕ)")
        print(f"          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 {q} {q2} g h")
        print(f"              - ramanujanGcdClassWindowAverageRat X0 {q2} h")
        print(f"                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q} g")
        print(f"              - ramanujanGcdClassWindowAverageRat X0 {q} g")
        print(f"                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 {q} {q2} {q2} h")
        print(f"              + ramanujanGcdClassWindowAverageRat X0 {q} g")
        print(f"                  * ramanujanGcdClassWindowAverageRat X0 {q2} h")
        print(f"                  * evenRamanujanBlockCountRat {q} {q2}))")
        term_names_by_g: dict[int, list[str]] = {g: [] for g in divs_q}
        row_values: dict[int, Fraction] = {g: Fraction(0, 1) for g in divs_q}
        for g in divs_q:
            avg_g = exact_ctx["avg_by_q"][q][g]
            left = Fraction(gcd_class_count_in_even_progression(q, g, first_even, even_count, exact_ctx), 1)
            c_g = exact_ctx["gcd_coeff_by_q"][q][g]
            for h in divs_q2:
                avg_h = exact_ctx["avg_by_q"][q2][h]
                right = Fraction(gcd_class_count_in_even_progression(q2, h, first_even, even_count, exact_ctx), 1)
                pair = Fraction(
                    gcd_class_pair_count_in_even_progression(q, q2, g, h, first_even, even_count, exact_ctx),
                    1,
                )
                c_h = exact_ctx["gcd_coeff_by_q"][q2][h]
                centered_full_block = pair - avg_h * left - avg_g * right + avg_g * avg_h * even_count_rat
                term_value = c_g * c_h * Fraction(full_blocks, 1) * centered_full_block
                term_name = f"hTerm_{g}_{h}"
                term_names_by_g[g].append(term_name)
                row_values[g] += term_value
                print(f"  have {term_name} :")
                print(f"      T {g} {h} = {fraction_to_q_literal(term_value)} := by")
                print("    dsimp [T]")
                print("    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,")
                print(
                    f"      hCoeffLeft_{g}, hCoeffRight_{h}, hAvgLeft_{g}, hAvgRight_{h}, "
                    f"hBlockLeft_{g}, hBlockRight_{h}, hPair_{g}_{h}]"
                )
        row_names: list[str] = []
        for g in divs_q:
            row_name = f"hRow_{g}"
            row_names.append(row_name)
            print(f"  have {row_name} :")
            print(f"      (∑ h ∈ Nat.divisors {q2}, T {g} h) = {fraction_to_q_literal(row_values[g])} := by")
            print("    norm_num [" + ", ".join(["hDivRight"] + term_names_by_g[g]) + "]")
        simp_args = [
            "centeredRamanujanPairBlockPeriod",
            "evenRamanujanBlockCountRat",
            "H",
            "hDivLeft",
            "hDivRight",
        ]
        simp_args.extend([f"hCoeffLeft_{g}" for g in divs_q])
        simp_args.extend([f"hCoeffRight_{h}" for h in divs_q2])
        simp_args.extend([f"hAvgLeft_{g}" for g in divs_q])
        simp_args.extend([f"hAvgRight_{h}" for h in divs_q2])
        simp_args.extend([f"hBlockLeft_{g}" for g in divs_q])
        simp_args.extend([f"hBlockRight_{h}" for h in divs_q2])
        simp_args.extend([f"hPair_{g}_{h}" for g in divs_q for h in divs_q2])
        print("  unfold centeredRamanujanPairPeriodicMainTermRat")
        print(f"  change (∑ g ∈ Nat.divisors {q}, ∑ h ∈ Nat.divisors {q2}, T g h) = {fraction_to_q_literal(centered_term)}")
        print("  rw [hDivLeft]")
        print("  simp [List.toFinset_cons, List.toFinset_nil, Finset.sum_insert,")
        print("    " + ", ".join(row_names) + "]")
        print("  norm_num")
        print()
        print(f"theorem {name}_orderedSummand :")
        print(f"    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk {q} {q2}) = {fraction_to_q_literal(summand_value)} := by")
        print(f"  have hneq : {q} ≠ {q2} := by")
        print("    norm_num")
        print(f"  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat {q} = {fraction_to_q_literal(coeff_q)} := by")
        print("    native_decide")
        print(f"  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat {q2} = {fraction_to_q_literal(coeff_q2)} := by")
        print("    native_decide")
        print(
            f"  have hvalue : ({fraction_to_q_literal(coeff_q)}) * ({fraction_to_q_literal(coeff_q2)}) "
            f"* ({fraction_to_q_literal(centered_term)}) = {fraction_to_q_literal(summand_value)} := by"
        )
        print("    norm_num")
        print("  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue")
        print("    hneq hCoeffLeft hCoeffRight")
        print(f"    {name}_centeredTerm")
        print("    hvalue")
        print()
        print("end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")
        return

    if args.combine_periodic_main_chunks:
        chunk_paths = list(args.combine_periodic_main_chunks)
        if not chunk_paths:
            raise SystemExit("--combine-periodic-main-chunks requires at least one JSON file")

        X_ref = None
        total_unordered_pairs_ref = None
        covered_ranges: list[tuple[int, int]] = []
        covered_pairs = 0
        active_nonzero_pairs = 0
        total = Fraction(0, 1)
        abs_total = Fraction(0, 1)
        total_elapsed_sec = 0.0
        elapsed_count = 0
        ordered_records: list[dict[str, object]] = []

        for path in chunk_paths:
            with open(path, "r", encoding="utf-8") as fh:
                payload = json.load(fh)
            if payload.get("mode") != "periodic-main-exact-chunk":
                raise SystemExit(f"{path}: not a periodic-main exact chunk payload")
            if X_ref is None:
                X_ref = int(payload["X"])
                total_unordered_pairs_ref = int(payload["total_unordered_pairs"])
            elif int(payload["X"]) != X_ref:
                raise SystemExit(f"{path}: mismatched X")
            elif int(payload["total_unordered_pairs"]) != total_unordered_pairs_ref:
                raise SystemExit(f"{path}: mismatched total_unordered_pairs")

            start_i, end_i = tuple(payload["pair_range"])
            covered_ranges.append((start_i, end_i))
            covered_pairs += end_i - start_i
            active_nonzero_pairs += int(payload["active_nonzero_pairs"])
            total += Fraction(int(payload["chunk_total_num"]), int(payload["chunk_total_den"]))
            abs_total += Fraction(int(payload["chunk_abs_total_num"]), int(payload["chunk_abs_total_den"]))
            for record in payload.get("nonzero_records", []):
                q = int(record["q"])
                q2 = int(record["q2"])
                signed = Fraction(int(record["signed_num"]), int(record["signed_den"]))
                ordered_value = signed / 2
                ordered_records.append({
                    "q": q,
                    "q2": q2,
                    "value_num": ordered_value.numerator,
                    "value_den": ordered_value.denominator,
                })
                ordered_records.append({
                    "q": q2,
                    "q2": q,
                    "value_num": ordered_value.numerator,
                    "value_den": ordered_value.denominator,
                })
            if "elapsed_sec" in payload:
                total_elapsed_sec += float(payload["elapsed_sec"])
                elapsed_count += 1

        sorted_ranges = sorted(covered_ranges)
        contiguous_to = 0
        missing_ranges: list[tuple[int, int]] = []
        for start_i, end_i in sorted_ranges:
            if start_i > contiguous_to:
                missing_ranges.append((contiguous_to, start_i))
                break
            contiguous_to = max(contiguous_to, end_i)
        ordered_record_total = Fraction(0, 1)
        seen_ordered_pairs: set[tuple[int, int]] = set()
        duplicate_ordered_pairs: list[tuple[int, int]] = []
        for record in ordered_records:
            pair = (int(record["q"]), int(record["q2"]))
            if pair in seen_ordered_pairs:
                duplicate_ordered_pairs.append(pair)
            seen_ordered_pairs.add(pair)
            ordered_record_total += Fraction(int(record["value_num"]), int(record["value_den"]))
        if ordered_record_total != total:
            raise SystemExit(
                "ordered periodic-main records do not sum to the combined chunk total: "
                f"{ordered_record_total} != {total}"
            )
        if duplicate_ordered_pairs:
            raise SystemExit(
                "ordered periodic-main records contain duplicate ordered pairs; "
                f"first duplicate = {duplicate_ordered_pairs[0]}"
            )

        print("Combined exact periodic-main chunk report")
        print(f"  X                       = {X_ref}")
        print(f"  chunk files             = {len(chunk_paths)}")
        print(f"  covered ranges          = {sorted_ranges}")
        print(f"  covered pairs           = {covered_pairs}")
        print(f"  total unordered pairs   = {total_unordered_pairs_ref}")
        print(f"  contiguous covered to   = {contiguous_to}")
        print(f"  missing ranges          = {missing_ranges}")
        print(f"  active nonzero pairs    = {active_nonzero_pairs}")
        print(f"  ordered nonzero records = {len(ordered_records)}")
        if elapsed_count > 0:
            print(f"  elapsed chunks          = {elapsed_count}")
            print(f"  chunk eval elapsed sec  = {total_elapsed_sec:.1f}")
            print(f"  avg sec per chunk       = {total_elapsed_sec / elapsed_count:.1f}")
            print(f"  avg ms per pair         = {(1000.0 * total_elapsed_sec) / max(covered_pairs, 1):.3f}")
        print(f"  periodic_main_q         = {fraction_to_q_literal(total)}")
        print(f"  periodic_main_abs_q     = {fraction_to_q_literal(abs_total)}")
        print()
        print("Lean-facing periodic-main certificate")
        print("def surrogatePeriodicMainX0RatCert : ℚ :=")
        print(f"  {fraction_to_q_literal(total)}")
        print()
        print("theorem surrogatePeriodicMainX0RatCert_abs_le_check :")
        print("    |(surrogatePeriodicMainX0RatCert : ℝ)| ≤ surrogatePeriodicMainX0Check.lhs := by")
        print("  norm_num [surrogatePeriodicMainX0RatCert, surrogatePeriodicMainX0Check]")
        if args.emit_periodic_main_ordered_records_json:
            out_payload = {
                "mode": "periodic-main-ordered-nonzero-records",
                "X": X_ref,
                "chunk_files": len(chunk_paths),
                "covered_pairs": covered_pairs,
                "total_unordered_pairs": total_unordered_pairs_ref,
                "unordered_nonzero_records": active_nonzero_pairs,
                "ordered_nonzero_records": len(ordered_records),
                "total_num": total.numerator,
                "total_den": total.denominator,
                "records": sorted(ordered_records, key=lambda r: (int(r["q"]), int(r["q2"]))),
            }
            with open(args.emit_periodic_main_ordered_records_json, "w", encoding="utf-8") as fh:
                json.dump(out_payload, fh, indent=2, sort_keys=True)
            print()
            print("Ordered periodic-main sparse-record payload")
            print(f"  wrote                   = {args.emit_periodic_main_ordered_records_json}")
            print(f"  records                 = {len(ordered_records)}")
        return

    if args.combine_boundary_chunks:
        top_remove_ref = None
        selected_patterns_ref = None
        total_active_blocks_ref = None
        X_ref = None
        covered_ranges: list[tuple[int, int]] = []
        chunk_paths = list(args.combine_boundary_chunks)

        with open(chunk_paths[0], "r", encoding="utf-8") as fh:
            first_payload = json.load(fh)

        if first_payload.get("mode") == "boundary-signed-split-exact-chunk":
            X_ref = int(first_payload["X"])
            total_active_blocks_ref = int(first_payload["total_active_blocks"])
            covered_blocks = 0
            active_total = Fraction(0, 1)
            active_abs_total = Fraction(0, 1)
            total_elapsed_sec = 0.0
            elapsed_count = 0

            for path in chunk_paths:
                with open(path, "r", encoding="utf-8") as fh:
                    payload = json.load(fh)
                if payload.get("mode") != "boundary-signed-split-exact-chunk":
                    raise SystemExit(f"{path}: not a boundary signed split exact chunk payload")
                if int(payload["X"]) != X_ref:
                    raise SystemExit(f"{path}: mismatched X")
                if int(payload["total_active_blocks"]) != total_active_blocks_ref:
                    raise SystemExit(f"{path}: mismatched total_active_blocks")
                start_i, end_i = tuple(payload["block_range"])
                covered_ranges.append((start_i, end_i))
                covered_blocks += len(payload.get("records", [])) or (end_i - start_i)
                active_total += Fraction(int(payload["chunk_total_num"]), int(payload["chunk_total_den"]))
                active_abs_total += Fraction(
                    int(payload["chunk_abs_total_num"]), int(payload["chunk_abs_total_den"])
                )
                if "elapsed_sec" in payload:
                    total_elapsed_sec += float(payload["elapsed_sec"])
                    elapsed_count += 1

            print("Combined exact boundary active chunk report")
            print(f"  X                      = {X_ref}")
            print(f"  chunk files            = {len(chunk_paths)}")
            print(f"  covered ranges         = {sorted(covered_ranges)}")
            print(f"  covered blocks         = {covered_blocks}")
            print(f"  total active blocks    = {total_active_blocks_ref}")
            if elapsed_count > 0:
                print(f"  elapsed chunks         = {elapsed_count}")
                print(f"  chunk eval elapsed sec = {total_elapsed_sec:.1f}")
                print(f"  avg sec per chunk      = {total_elapsed_sec / elapsed_count:.1f}")
                print(f"  avg ms per block       = {(1000.0 * total_elapsed_sec) / covered_blocks:.3f}")
            print(f"  active_signed_q        = {fraction_to_q_literal(active_total)}")
            print(f"  active_abs_q           = {fraction_to_q_literal(active_abs_total)}")
            print()
            print("def surrogateBoundaryX0ActiveSignedGenerated : ℚ :=")
            print(f"  {fraction_to_q_literal(active_total)}")
            if args.emit_boundary_final_certificate:
                if not args.boundary_full_signed_decimal:
                    raise SystemExit("--emit-boundary-final-certificate requires --boundary-full-signed-decimal")
                full_frac = decimal_string_to_fraction(args.boundary_full_signed_decimal)
                inactive_frac = full_frac - active_total
                print()
                print("Lean-facing boundary final certificate")
                print(f"  active_signed_q           = {fraction_to_q_literal(active_total)}")
                print(f"  inactive_correction_q     = {fraction_to_q_literal(inactive_frac)}")
                print(f"  full_boundary_decimal_q   = {fraction_to_q_literal(full_frac)}")
                print()
                print("def surrogateBoundaryX0ActiveSignedCert : ℚ :=")
                print(f"  {fraction_to_q_literal(active_total)}")
                print()
                print("def surrogateBoundaryX0InactiveCorrectionCert : ℚ :=")
                print(f"  {fraction_to_q_literal(inactive_frac)}")
                print()
                print("def surrogateBoundaryX0FullCert : ℚ :=")
                print("  surrogateBoundaryX0ActiveSignedCert + surrogateBoundaryX0InactiveCorrectionCert")
            return

        def rec_key(rec: dict[str, object]) -> tuple[float, float, int, int, int, int]:
            pattern = tuple(rec["pattern"])
            G = int(rec["G"])
            return (
                float(rec["abs"]),
                abs(float(rec["signed"])),
                int(rec["pair_count"]),
                G,
                pattern[0],
                pattern[1],
            )

        # Pass 1: metadata validation + global top-N heap by the same ordering used in the
        # in-memory classifier.
        top_heap: list[tuple[tuple[float, float, int, int, int, int], tuple[tuple[int, int], int]]] = []
        top_seen: set[tuple[tuple[int, int], int]] = set()

        for path in chunk_paths:
            with open(path, "r", encoding="utf-8") as fh:
                payload = json.load(fh)
            if payload.get("mode") != "boundary-signed-split-chunk":
                raise SystemExit(f"{path}: not a boundary signed split chunk payload")
            if top_remove_ref is None:
                top_remove_ref = int(payload["top_remove"])
                selected_patterns_ref = {tuple(p) for p in payload["selected_patterns"]}
                total_active_blocks_ref = int(payload["total_active_blocks"])
                X_ref = int(payload["X"])
            else:
                if int(payload["top_remove"]) != top_remove_ref:
                    raise SystemExit(f"{path}: mismatched top_remove")
                if {tuple(p) for p in payload["selected_patterns"]} != selected_patterns_ref:
                    raise SystemExit(f"{path}: mismatched selected_patterns")
                if int(payload["total_active_blocks"]) != total_active_blocks_ref:
                    raise SystemExit(f"{path}: mismatched total_active_blocks")
                if int(payload["X"]) != X_ref:
                    raise SystemExit(f"{path}: mismatched X")
            covered_ranges.append(tuple(payload["block_range"]))
            for rec in payload["records"]:
                pattern = tuple(rec["pattern"])
                G = int(rec["G"])
                key = (pattern, G)
                if key in top_seen:
                    raise SystemExit(f"{path}: duplicate block record for {key}")
                top_seen.add(key)
                if (top_remove_ref or 0) <= 0:
                    continue
                score = rec_key(rec)
                if len(top_heap) < (top_remove_ref or 0):
                    heapq.heappush(top_heap, (score, key))
                elif score > top_heap[0][0]:
                    heapq.heapreplace(top_heap, (score, key))

        top_global_blocks = {key for _, key in top_heap}
        selected_patterns = selected_patterns_ref or set()
        coherent_threshold = 1.0 - 1e-12
        selected_signed = 0.0
        selected_abs = 0.0
        coh2_signed = 0.0
        coh2_abs = 0.0
        incoh_signed = 0.0
        incoh_abs = 0.0
        covered_blocks = 0

        # Pass 2: stream totals without materializing all blocks.
        for path in chunk_paths:
            with open(path, "r", encoding="utf-8") as fh:
                payload = json.load(fh)
            for rec in payload["records"]:
                pattern = tuple(rec["pattern"])
                G = int(rec["G"])
                key = (pattern, G)
                signed = float(rec["signed"])
                abs_val = float(rec["abs"])
                pair_count = int(rec["pair_count"])
                covered_blocks += 1
                if key in top_global_blocks or pattern in selected_patterns:
                    selected_signed += signed
                    selected_abs += abs_val
                elif pair_count == 2 and ((abs(signed) / abs_val) if abs_val else 0.0) >= coherent_threshold:
                    coh2_signed += signed
                    coh2_abs += abs_val
                else:
                    incoh_signed += signed
                    incoh_abs += abs_val

        total_signed = selected_signed + coh2_signed + incoh_signed
        total_abs = selected_abs + coh2_abs + incoh_abs

        print("Combined boundary chunk report")
        print(f"  X                      = {X_ref}")
        print(f"  chunk files            = {len(chunk_paths)}")
        print(f"  covered ranges         = {sorted(covered_ranges)}")
        print(f"  covered blocks         = {covered_blocks}")
        print(f"  total active blocks    = {total_active_blocks_ref}")
        print(f"  top_remove             = {top_remove_ref}")
        print(f"  selected patterns      = {sorted(selected_patterns)}")
        print()
        print("  combined active-scope split")
        print(f"    selected_signed      = {selected_signed:.12e}")
        print(f"    selected_abs         = {selected_abs:.12e}")
        print(f"    coh2_signed          = {coh2_signed:.12e}")
        print(f"    coh2_abs             = {coh2_abs:.12e}")
        print(f"    incoh_signed         = {incoh_signed:.12e}")
        print(f"    incoh_abs            = {incoh_abs:.12e}")
        print(f"    total_signed         = {total_signed:.12e}")
        print(f"    abs(total_signed)    = {abs(total_signed):.12e}")
        print(f"    total_abs            = {total_abs:.12e}")
        if args.emit_boundary_final_certificate:
            if not args.boundary_full_signed_decimal:
                raise SystemExit("--emit-boundary-final-certificate requires --boundary-full-signed-decimal")
            active_frac = float_to_fixed_fraction(total_signed)
            full_frac = decimal_string_to_fraction(args.boundary_full_signed_decimal)
            inactive_frac = full_frac - active_frac
            print()
            print("Lean-facing boundary final certificate")
            print(f"  active_signed_decimal     = {float(active_frac):.12f}")
            print(f"  inactive_correction       = {float(inactive_frac):.12f}")
            print(f"  full_boundary_decimal     = {float(full_frac):.12f}")
            print()
            print("def surrogateBoundaryX0ActiveSignedCert : ℚ :=")
            print(f"  {fraction_to_q_literal(active_frac)}")
            print()
            print("def surrogateBoundaryX0InactiveCorrectionCert : ℚ :=")
            print(f"  {fraction_to_q_literal(inactive_frac)}")
            print()
            print("def surrogateBoundaryX0FullCert : ℚ :=")
            print("  surrogateBoundaryX0ActiveSignedCert + surrogateBoundaryX0InactiveCorrectionCert")
            print()
            print("theorem surrogateBoundaryX0FullCert_abs_le_check :")
            print("    |(surrogateBoundaryX0FullCert : ℝ)| ≤ surrogateBoundaryX0Check.lhs := by")
            print("  norm_num [surrogateBoundaryX0FullCert,")
            print("            surrogateBoundaryX0ActiveSignedCert,")
            print("            surrogateBoundaryX0InactiveCorrectionCert,")
            print("            surrogateBoundaryX0Check]")
        return

    X = args.X
    q_active_max = args.q_max_active

    true_c2 = None
    true_c2_abs_error = None
    scale_factor = 1.0
    scale_factor_abs_error = 0.0
    scale_sq = 1.0
    scale_sq_abs_error = 0.0

    if args.true_series:
        true_c2, true_c2_abs_error = true_c2_from_odd_prime_euler_product(args.true_prime_cutoff)
        scale_factor = C2_NUMERIC / true_c2
        scale_sq = scale_factor * scale_factor
        true_c2_lo = max(true_c2 - true_c2_abs_error, 1e-300)
        true_c2_hi = true_c2 + true_c2_abs_error
        scale_sq_lo = (C2_NUMERIC / true_c2_hi) ** 2
        scale_sq_hi = (C2_NUMERIC / true_c2_lo) ** 2
        scale_sq_abs_error = max(abs(scale_sq - scale_sq_lo), abs(scale_sq_hi - scale_sq))

    mu, phi = mobius_phi_sieve(Q0)
    spf = spf_sieve(Q0)
    primes = primes_from_spf(spf)

    support = coeff_support(Q0, mu)
    active_support = [q for q in support if q <= q_active_max]
    even_window = even_window_points(X)
    even_window_card = len(even_window)

    if args.emit_periodic_main_row_exact_json:
        if args.true_series:
            raise SystemExit("--emit-periodic-main-row-exact-json is only implemented for the surrogate normalization")
        row_s, out_path = args.emit_periodic_main_row_exact_json
        emit_periodic_main_row_exact_json(
            X=X,
            row=int(row_s),
            active_support=active_support,
            mu=mu,
            phi=phi,
            spf=spf,
            even_window_card=even_window_card,
            out_path=out_path,
            progress=args.progress,
            progress_every=max(1, args.progress_every),
        )
        return

    if args.emit_periodic_main_zero_records_json:
        if args.true_series:
            raise SystemExit("--emit-periodic-main-zero-records-json is only implemented for the surrogate normalization")
        nonzero_path, out_path = args.emit_periodic_main_zero_records_json
        with open(nonzero_path, "r", encoding="utf-8") as fh:
            payload = json.load(fh)
        if payload.get("mode") != "periodic-main-ordered-nonzero-records":
            raise SystemExit(f"{nonzero_path}: not a periodic-main ordered-nonzero-record payload")
        if int(payload.get("X", X)) != X:
            raise SystemExit(f"{nonzero_path}: payload X={payload.get('X')} does not match --X {X}")
        nonzero_pairs = {
            (int(record["q"]), int(record["q2"]))
            for record in payload.get("records", [])
        }
        full_block_ordered_pairs = [
            (q, q2)
            for q in active_support
            for q2 in active_support
            if q != q2 and block_period(q, q2) <= H + 1
        ]
        full_block_pair_set = set(full_block_ordered_pairs)
        extra_nonzero = sorted(nonzero_pairs - full_block_pair_set)
        if extra_nonzero:
            raise SystemExit(
                "nonzero records contain pairs outside full-block support; "
                f"first extra pair = {extra_nonzero[0]}"
            )
        zero_records = [
            {
                "q": q,
                "q2": q2,
                "value_num": 0,
                "value_den": 1,
            }
            for q, q2 in full_block_ordered_pairs
            if (q, q2) not in nonzero_pairs
        ]
        out_payload = {
            "mode": "periodic-main-ordered-zero-records",
            "X": X,
            "active_support_card": len(active_support),
            "full_block_ordered_pairs": len(full_block_ordered_pairs),
            "ordered_nonzero_records": len(nonzero_pairs),
            "ordered_zero_records": len(zero_records),
            "records": zero_records,
        }
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(out_payload, fh, indent=2, sort_keys=True)
        print("Periodic-main ordered zero-record payload")
        print(f"  X                         = {X}")
        print(f"  active support card       = {len(active_support)}")
        print(f"  full-block ordered pairs  = {len(full_block_ordered_pairs)}")
        print(f"  ordered nonzero records   = {len(nonzero_pairs)}")
        print(f"  ordered zero records      = {len(zero_records)}")
        print(f"  wrote                     = {out_path}")
        return

    def log_exact_progress(
        processed: int,
        total_pairs: int,
        nonzero_count: int,
        total: Fraction,
        started: float,
    ) -> None:
        if not args.progress:
            return
        elapsed = time.time() - started
        pct = (100.0 * processed / total_pairs) if total_pairs else 0.0
        print(
            f"[boundary-rat] processed={processed}/{total_pairs} ({pct:.2f}%) "
            f"nonzero={nonzero_count} num_bits={total.numerator.bit_length()} "
            f"den_bits={total.denominator.bit_length()} elapsed={elapsed:.1f}s",
            file=sys.stderr,
            flush=True,
        )
        if args.checkpoint_json:
            with open(args.checkpoint_json, "w", encoding="utf-8") as f:
                json.dump(
                    {
                        "processed_pairs": processed,
                        "total_pairs": total_pairs,
                        "nonzero_count": nonzero_count,
                        "numerator_bit_length": total.numerator.bit_length(),
                        "denominator_bit_length": total.denominator.bit_length(),
                        "elapsed_seconds": elapsed,
                    },
                    f,
                    indent=2,
                    sort_keys=True,
                )

    if args.boundary_signed_split_fast:
        if args.true_series:
            raise SystemExit("--boundary-signed-split-fast is only implemented for the surrogate normalization")

        selected_patterns = parse_selected_patterns(args.boundary_family_patterns)
        block_scope = active_support
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            block_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )
        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, block_scope,
            progress=args.progress,
        )

        all_blocks = list(pair_count_by_block.keys())
        total_active_blocks = len(all_blocks)
        start = 0
        end = total_active_blocks
        if args.block_range is not None:
            start, end = args.block_range
            if start < 0 or end < start:
                raise SystemExit("--block-range must satisfy 0 <= START <= END")
            start = min(start, total_active_blocks)
            end = min(end, total_active_blocks)
            all_blocks = all_blocks[start:end]

        signed_by_block: dict[tuple[tuple[int, int], int], float] = {}
        abs_by_block: dict[tuple[tuple[int, int], int], float] = {}
        block_progress_every = min(max(args.progress_every, 1), 50_000)
        processed = 0
        started = time.time()
        for pattern, G in all_blocks:
            q = G * pattern[0]
            q2 = G * pattern[1]
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            block = (pattern, G)
            signed_by_block[block] = val
            abs_by_block[block] = abs(val)
            processed += 1
            if args.progress and processed % block_progress_every == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-signed-split-fast] processed_blocks={processed}/{len(all_blocks)} "
                    f"elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        if args.block_range is not None:
            records = []
            for block in all_blocks:
                pattern, G = block
                records.append({
                    "pattern": [pattern[0], pattern[1]],
                    "G": G,
                    "pair_count": pair_count_by_block[block],
                    "signed": signed_by_block[block],
                    "abs": abs_by_block[block],
                })
            payload = {
                "mode": "boundary-signed-split-chunk",
                "X": X,
                "active_ordered_pairs": total_pairs,
                "active_support_card": len(active_support),
                "block_range": [start, end],
                "top_remove": max(args.boundary_pattern_g_remove_top, 0),
                "selected_patterns": [list(p) for p in sorted(selected_patterns)],
                "total_active_blocks": total_active_blocks,
                "records": records,
            }
            if args.checkpoint_json:
                with open(args.checkpoint_json, "w", encoding="utf-8") as fh:
                    json.dump(payload, fh, indent=2, sort_keys=True)
            print("Boundary signed split fast chunk report")
            print(f"  X                        = {X}")
            print(f"  active ordered pairs     = {total_pairs}")
            print(f"  total active blocks      = {total_active_blocks}")
            print(f"  block range              = [{start}, {end})")
            print(f"  evaluated chunk blocks   = {len(all_blocks)}")
            print(f"  chunk signed total       = {math.fsum(signed_by_block.values()):.12e}")
            print(f"  chunk abs total          = {math.fsum(abs_by_block.values()):.12e}")
            if args.checkpoint_json:
                print(f"  wrote checkpoint json    = {args.checkpoint_json}")
            return

        classified = classify_signed_boundary_blocks(
            pair_count_by_block,
            signed_by_block,
            abs_by_block,
            top_remove=max(args.boundary_pattern_g_remove_top, 0),
            selected_patterns=selected_patterns,
        )
        total_signed = (
            classified["selected_signed"]
            + classified["coh2_signed"]
            + classified["incoh_signed"]
        )
        total_abs = (
            classified["selected_abs"]
            + classified["coh2_abs"]
            + classified["incoh_abs"]
        )
        print("Boundary signed split fast report")
        print(f"  X                        = {X}")
        print(f"  active support card      = {len(active_support)}")
        print(f"  active ordered pairs     = {total_pairs}")
        print(f"  distinct active blocks   = {total_active_blocks}")
        print(f"  top global blocks selected = {min(max(args.boundary_pattern_g_remove_top, 0), total_active_blocks)}")
        print(f"  expanded family patterns   = {sorted(selected_patterns)}")
        print()
        print("  active-scope signed split")
        print(f"    selected_signed        = {classified['selected_signed']:.12e}")
        print(f"    selected_abs           = {classified['selected_abs']:.12e}")
        print(f"    coh2_signed            = {classified['coh2_signed']:.12e}")
        print(f"    coh2_abs               = {classified['coh2_abs']:.12e}")
        print(f"    incoh_signed           = {classified['incoh_signed']:.12e}")
        print(f"    incoh_abs              = {classified['incoh_abs']:.12e}")
        print(f"    total_signed           = {total_signed:.12e}")
        print(f"    abs(total_signed)      = {abs(total_signed):.12e}")
        print(f"    total_abs              = {total_abs:.12e}")
        return

    if args.periodic_main_exact_parallel:
        if args.true_series:
            raise SystemExit("--periodic-main-exact-parallel is only implemented for the surrogate normalization")
        if args.batch_size <= 0:
            raise SystemExit("--periodic-main-exact-parallel requires --batch-size N")
        if args.block_range is None:
            raise SystemExit("--periodic-main-exact-parallel requires --block-range START END")
        if not args.checkpoint_dir:
            raise SystemExit("--periodic-main-exact-parallel requires --checkpoint-dir DIR")
        if args.workers <= 1:
            raise SystemExit("--periodic-main-exact-parallel requires --workers >= 2")

        all_pairs = [
            (q, q2)
            for i, q in enumerate(active_support)
            for q2 in active_support[i + 1:]
        ]
        total_unordered_pairs = len(all_pairs)
        start, end = args.block_range
        if start < 0 or end < start:
            raise SystemExit("--block-range must satisfy 0 <= START <= END")
        start = min(start, total_unordered_pairs)
        end = min(end, total_unordered_pairs)
        all_pairs = all_pairs[start:end]

        q_needed_exact: set[int] = set()
        for q, q2 in all_pairs:
            q_needed_exact.add(q)
            q_needed_exact.add(q2)

        exact_ctx = build_surrogate_boundary_exact_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed_exact),
            progress=args.progress,
            progress_every_q=max(1, args.progress_every),
        )

        os.makedirs(args.checkpoint_dir, exist_ok=True)
        meta_path = os.path.join(args.checkpoint_dir, "periodic_main_exact_batch_meta.json")
        with open(meta_path, "w", encoding="utf-8") as fh:
            json.dump(
                {
                    "mode": "periodic-main-exact-batch-meta",
                    "parallel": True,
                    "workers": args.workers,
                    "X": X,
                    "total_unordered_pairs": total_unordered_pairs,
                    "requested_start": start,
                    "requested_end": end,
                    "batch_size": args.batch_size,
                    "active_support_card": len(active_support),
                    "status": "setup_complete",
                },
                fh,
                indent=2,
                sort_keys=True,
            )
        print(
            f"[periodic-main-exact-parallel] setup complete "
            f"pairs={total_unordered_pairs} range=[{start},{end}) batch_size={args.batch_size} workers={args.workers}",
            flush=True,
        )
        global _PERIODIC_MAIN_EXACT_PARALLEL_GLOBALS
        _PERIODIC_MAIN_EXACT_PARALLEL_GLOBALS = {
            "X": X,
            "exact_ctx": exact_ctx,
            "total_unordered_pairs": total_unordered_pairs,
            "active_support_card": len(active_support),
            "progress": args.progress,
            "progress_every": args.progress_every,
            "checkpoint_dir": args.checkpoint_dir,
            "skip_existing_chunks": args.skip_existing_chunks,
            "start": start,
            "all_pairs": all_pairs,
        }
        tasks = [
            (chunk_start, min(chunk_start + args.batch_size, end))
            for chunk_start in range(start, end, args.batch_size)
        ]
        wrote = 0
        skipped = 0
        total_chunk_elapsed = 0.0
        ctx_mp = multiprocessing.get_context("fork")
        with ctx_mp.Pool(processes=args.workers) as pool:
            for result in pool.imap_unordered(_periodic_main_exact_parallel_worker, tasks):
                if result["status"] == "skipped":
                    skipped += 1
                    continue
                wrote += 1
                total_chunk_elapsed += float(result["elapsed_sec"])
                print(
                    f"[periodic-main-exact-parallel] wrote {result['out_path']} "
                    f"elapsed={float(result['elapsed_sec']):.1f}s "
                    f"total={fraction_to_q_literal(Fraction(int(result['chunk_total_num']), int(result['chunk_total_den'])))}",
                    flush=True,
                )
        print("Periodic-main exact parallel batch report")
        print(f"  X                         = {X}")
        print(f"  total unordered pairs     = {total_unordered_pairs}")
        print(f"  requested range           = [{start}, {end})")
        print(f"  batch size                = {args.batch_size}")
        print(f"  workers                   = {args.workers}")
        print(f"  checkpoint dir            = {args.checkpoint_dir}")
        print(f"  chunks written            = {wrote}")
        print(f"  chunks skipped            = {skipped}")
        if wrote > 0:
            print(f"  chunk eval elapsed sec    = {total_chunk_elapsed:.1f}")
            print(f"  avg sec per written chunk = {total_chunk_elapsed / wrote:.1f}")
        return

    if args.boundary_signed_split_exact or args.boundary_signed_split_exact_parallel:
        if args.true_series:
            raise SystemExit("--boundary-signed-split-exact is only implemented for the surrogate normalization")

        block_scope = active_support
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            block_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        all_blocks = list(pair_count_by_block.keys())
        total_active_blocks = len(all_blocks)
        start = 0
        end = total_active_blocks
        if args.block_range is not None:
            start, end = args.block_range
            if start < 0 or end < start:
                raise SystemExit("--block-range must satisfy 0 <= START <= END")
            start = min(start, total_active_blocks)
            end = min(end, total_active_blocks)
            all_blocks = all_blocks[start:end]

        q_needed_exact: set[int] = set()
        for pattern, G in all_blocks:
            m, n = pattern
            q_needed_exact.add(G * m)
            q_needed_exact.add(G * n)

        exact_ctx = build_surrogate_boundary_exact_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed_exact),
            progress=args.progress,
            progress_every_q=max(1, args.progress_every),
        )

        def eval_exact_chunk(
            chunk_start: int,
            chunk_end: int,
            chunk_blocks: list[tuple[tuple[int, int], int]],
            *,
            include_records: bool,
        ) -> tuple[dict[str, object], float]:
            block_progress_every = min(
                max(1, min(max(args.progress_every, 1), max(1, len(chunk_blocks) // 10))),
                50_000,
            )
            processed = 0
            started = time.time()
            records = [] if include_records else None
            chunk_total = Fraction(0, 1)
            chunk_abs_total = Fraction(0, 1)
            for pattern, G in chunk_blocks:
                m, n = pattern
                q = G * m
                q2 = G * n
                val = 2 * surrogate_boundary_pair_contribution_rat_cached(X, q, q2, exact_ctx)
                abs_val = abs(val)
                chunk_total += val
                chunk_abs_total += abs_val
                if records is not None:
                    records.append({
                        "pattern": [pattern[0], pattern[1]],
                        "G": G,
                        "pair_count": pair_count_by_block[(pattern, G)],
                        "signed_num": val.numerator,
                        "signed_den": val.denominator,
                        "abs_num": abs_val.numerator,
                        "abs_den": abs_val.denominator,
                        "signed_q": fraction_to_q_literal(val),
                        "abs_q": fraction_to_q_literal(abs_val),
                    })
                processed += 1
                if args.progress and processed % block_progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-signed-split-exact] processed_blocks={processed}/{len(chunk_blocks)} "
                        f"chunk=[{chunk_start},{chunk_end}) elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

            elapsed_sec = time.time() - started
            payload = {
                "mode": "boundary-signed-split-exact-chunk",
                "X": X,
                "active_support_card": len(active_support),
                "active_ordered_pairs": total_pairs,
                "total_active_blocks": total_active_blocks,
                "block_range": [chunk_start, chunk_end],
                "start": chunk_start,
                "end": chunk_end,
                "chunk_total_num": chunk_total.numerator,
                "chunk_total_den": chunk_total.denominator,
                "chunk_abs_total_num": chunk_abs_total.numerator,
                "chunk_abs_total_den": chunk_abs_total.denominator,
                "elapsed_sec": elapsed_sec,
            }
            if records is not None:
                payload["records"] = records
            return payload, elapsed_sec

        if args.boundary_signed_split_exact_parallel:
            if args.batch_size <= 0:
                raise SystemExit("--boundary-signed-split-exact-parallel requires --batch-size N")
            if args.block_range is None:
                raise SystemExit("--boundary-signed-split-exact-parallel requires --block-range START END")
            if not args.checkpoint_dir:
                raise SystemExit("--boundary-signed-split-exact-parallel requires --checkpoint-dir DIR")
            if args.workers <= 1:
                raise SystemExit("--boundary-signed-split-exact-parallel requires --workers >= 2")
            os.makedirs(args.checkpoint_dir, exist_ok=True)
            meta_path = os.path.join(args.checkpoint_dir, "boundary_active_exact_batch_meta.json")
            with open(meta_path, "w", encoding="utf-8") as fh:
                json.dump(
                    {
                        "mode": "boundary-signed-split-exact-batch-meta",
                        "parallel": True,
                        "workers": args.workers,
                        "X": X,
                        "total_active_blocks": total_active_blocks,
                        "requested_start": start,
                        "requested_end": end,
                        "batch_size": args.batch_size,
                        "active_support_card": len(active_support),
                        "active_ordered_pairs": total_pairs,
                        "status": "setup_complete",
                    },
                    fh,
                    indent=2,
                    sort_keys=True,
                )
            print(
                f"[boundary-signed-split-exact-parallel] setup complete "
                f"blocks={total_active_blocks} range=[{start},{end}) batch_size={args.batch_size} workers={args.workers}",
                flush=True,
            )
            global _BOUNDARY_EXACT_PARALLEL_GLOBALS
            _BOUNDARY_EXACT_PARALLEL_GLOBALS = {
                "X": X,
                "exact_ctx": exact_ctx,
                "total_pairs": total_pairs,
                "total_active_blocks": total_active_blocks,
                "active_support_card": len(active_support),
                "progress": args.progress,
                "progress_every": args.progress_every,
                "checkpoint_dir": args.checkpoint_dir,
                "skip_existing_chunks": args.skip_existing_chunks,
                "start": start,
                "all_blocks": all_blocks,
            }
            tasks = [
                (chunk_start, min(chunk_start + args.batch_size, end))
                for chunk_start in range(start, end, args.batch_size)
            ]
            wrote = 0
            skipped = 0
            total_chunk_elapsed = 0.0
            ctx_mp = multiprocessing.get_context("fork")
            with ctx_mp.Pool(processes=args.workers) as pool:
                for result in pool.imap_unordered(_boundary_exact_parallel_worker, tasks):
                    if result["status"] == "skipped":
                        skipped += 1
                        continue
                    wrote += 1
                    total_chunk_elapsed += float(result["elapsed_sec"])
                    print(
                        f"[boundary-signed-split-exact-parallel] wrote {result['out_path']} "
                        f"elapsed={float(result['elapsed_sec']):.1f}s "
                        f"total={fraction_to_q_literal(Fraction(int(result['chunk_total_num']), int(result['chunk_total_den'])))}",
                        flush=True,
                    )
            print("Boundary signed split exact parallel batch report")
            print(f"  X                        = {X}")
            print(f"  total active blocks      = {total_active_blocks}")
            print(f"  requested range          = [{start}, {end})")
            print(f"  batch size               = {args.batch_size}")
            print(f"  workers                  = {args.workers}")
            print(f"  checkpoint dir           = {args.checkpoint_dir}")
            print(f"  chunks written           = {wrote}")
            print(f"  chunks skipped           = {skipped}")
            if wrote > 0:
                print(f"  chunk eval elapsed sec   = {total_chunk_elapsed:.1f}")
                print(f"  avg sec per written chunk = {total_chunk_elapsed / wrote:.1f}")
            return

        if args.batch_size > 0:
            if args.block_range is None:
                raise SystemExit("--batch-size requires --block-range START END")
            if not args.checkpoint_dir:
                raise SystemExit("--batch-size requires --checkpoint-dir DIR")
            os.makedirs(args.checkpoint_dir, exist_ok=True)
            meta_path = os.path.join(args.checkpoint_dir, "boundary_active_exact_batch_meta.json")
            with open(meta_path, "w", encoding="utf-8") as fh:
                json.dump(
                    {
                        "mode": "boundary-signed-split-exact-batch-meta",
                        "X": X,
                        "total_active_blocks": total_active_blocks,
                        "requested_start": start,
                        "requested_end": end,
                        "batch_size": args.batch_size,
                        "active_support_card": len(active_support),
                        "active_ordered_pairs": total_pairs,
                        "status": "setup_complete",
                    },
                    fh,
                    indent=2,
                    sort_keys=True,
                )
            print(
                f"[boundary-signed-split-exact-batch] setup complete "
                f"blocks={total_active_blocks} range=[{start},{end}) batch_size={args.batch_size}",
                flush=True,
            )
            wrote = 0
            skipped = 0
            total_chunk_elapsed = 0.0
            for chunk_start in range(start, end, args.batch_size):
                chunk_end = min(chunk_start + args.batch_size, end)
                out_path = os.path.join(
                    args.checkpoint_dir,
                    f"boundary_active_exact_chunk_{chunk_start:07d}_{chunk_end:07d}.json",
                )
                if args.skip_existing_chunks and os.path.exists(out_path):
                    skipped += 1
                    continue
                print(
                    f"[boundary-signed-split-exact-batch] begin chunk [{chunk_start},{chunk_end})",
                    flush=True,
                )
                payload, elapsed_sec = eval_exact_chunk(
                    chunk_start,
                    chunk_end,
                    all_blocks[chunk_start - start:chunk_end - start],
                    include_records=False,
                )
                with open(out_path, "w", encoding="utf-8") as fh:
                    json.dump(payload, fh, indent=2, sort_keys=True)
                wrote += 1
                total_chunk_elapsed += elapsed_sec
                print(
                    f"[boundary-signed-split-exact-batch] wrote {out_path} "
                    f"elapsed={elapsed_sec:.1f}s "
                    f"total={fraction_to_q_literal(Fraction(int(payload['chunk_total_num']), int(payload['chunk_total_den'])))}",
                    flush=True,
                )
            print("Boundary signed split exact batch report")
            print(f"  X                        = {X}")
            print(f"  total active blocks      = {total_active_blocks}")
            print(f"  requested range          = [{start}, {end})")
            print(f"  batch size               = {args.batch_size}")
            print(f"  checkpoint dir           = {args.checkpoint_dir}")
            print(f"  chunks written           = {wrote}")
            print(f"  chunks skipped           = {skipped}")
            if wrote > 0:
                print(f"  chunk eval elapsed sec   = {total_chunk_elapsed:.1f}")
                print(f"  avg sec per written chunk = {total_chunk_elapsed / wrote:.1f}")
            return

        payload, _elapsed_sec = eval_exact_chunk(start, end, all_blocks, include_records=True)
        if args.checkpoint_json:
            with open(args.checkpoint_json, "w", encoding="utf-8") as fh:
                json.dump(payload, fh, indent=2, sort_keys=True)

        print("Boundary signed split exact chunk report")
        print(f"  X                        = {X}")
        print(f"  active ordered pairs     = {total_pairs}")
        print(f"  total active blocks      = {total_active_blocks}")
        print(f"  block range              = [{start}, {end})")
        print(f"  evaluated chunk blocks   = {len(all_blocks)}")
        print(
            f"  chunk signed total       = "
            f"{fraction_to_q_literal(Fraction(int(payload['chunk_total_num']), int(payload['chunk_total_den'])))}"
        )
        print(
            f"  chunk abs total          = "
            f"{fraction_to_q_literal(Fraction(int(payload['chunk_abs_total_num']), int(payload['chunk_abs_total_den'])))}"
        )
        if args.checkpoint_json:
            print(f"  wrote checkpoint json    = {args.checkpoint_json}")
        return

    if args.boundary_zero_prune_report:
        if args.true_series:
            raise SystemExit("--boundary-zero-prune-report is only implemented for the surrogate normalization")
        total_pairs = len(support) * max(len(support) - 1, 0)
        zero_mode_pairs = 0
        zero_remainder_pairs = 0
        survivors = 0
        processed = 0
        started = time.time()
        for q in support:
            for q2 in support:
                if q == q2:
                    continue
                processed += 1
                if q in (1, 2) or q2 in (1, 2):
                    zero_mode_pairs += 1
                    continue
                if ((H + 1) % block_period(q, q2)) == 0:
                    zero_remainder_pairs += 1
                    continue
                survivors += 1
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-prune] processed={processed}/{total_pairs} "
                        f"zero_mode={zero_mode_pairs} zero_remainder={zero_remainder_pairs} "
                        f"survivors={survivors} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )
        print("Surrogate boundary cheap zero-prune report")
        print(f"  support ordered pairs     = {total_pairs}")
        print(f"  q in {{1,2}} zero pairs   = {zero_mode_pairs}")
        print(f"  zero remainder pairs      = {zero_remainder_pairs}")
        print(f"  survivors after cheap prune = {survivors}")
        return

    if args.boundary_period_group_report:
        if args.true_series:
            raise SystemExit("--boundary-period-group-report is only implemented for the surrogate normalization")

        period_scope = active_support if args.boundary_period_group_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in period_scope}

        pair_count_by_P: dict[int, int] = defaultdict(int)
        abs_coeff_proxy_by_P: dict[int, float] = defaultdict(float)
        coeff_sum_by_P: dict[int, float] = defaultdict(float)

        total_pairs = len(period_scope) * max(len(period_scope) - 1, 0)
        processed = 0
        started = time.time()
        for q in period_scope:
            cq = coeff_scope[q]
            for q2 in period_scope:
                if q == q2:
                    continue
                processed += 1
                P = block_period(q, q2)
                pair_count_by_P[P] += 1
                prod = cq * coeff_scope[q2]
                abs_coeff_proxy_by_P[P] += abs(prod)
                coeff_sum_by_P[P] += prod
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-period:group-pass1] processed={processed}/{total_pairs} "
                        f"groups={len(pair_count_by_P)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        top_k = max(args.boundary_period_group_top, 1)
        top_groups = sorted(
            pair_count_by_P.keys(),
            key=lambda P: (abs_coeff_proxy_by_P[P], pair_count_by_P[P], -P),
            reverse=True,
        )[:top_k]
        top_group_set = set(top_groups)

        q_needed: set[int] = set()
        for q in period_scope:
            for q2 in period_scope:
                if q == q2:
                    continue
                P = block_period(q, q2)
                if P in top_group_set:
                    q_needed.add(q)
                    q_needed.add(q2)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )
        float_total_by_P: dict[int, float] = defaultdict(float)

        processed = 0
        started = time.time()
        for q in period_scope:
            for q2 in period_scope:
                if q == q2:
                    continue
                P = block_period(q, q2)
                if P not in top_group_set:
                    continue
                processed += 1
                float_total_by_P[P] += surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-period:group-pass2] processed={processed} "
                        f"top_groups={len(top_group_set)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        print("Surrogate boundary period-group report")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_period_group_scope}")
        print(f"  support card              = {len(period_scope)}")
        print(f"  ordered offdiag pairs     = {total_pairs}")
        print(f"  distinct period groups    = {len(pair_count_by_P)}")
        print(f"  top groups by abs coeff proxy = {top_k}")
        print()
        print("  P         pairs        X mod P   (H+1) mod P   abs coeff proxy      coeff sum proxy       float boundary approx")
        for P in top_groups:
            print(
                f"  {P:>8}  {pair_count_by_P[P]:>10}  {X % P:>8}  {(H + 1) % P:>12}  "
                f"{abs_coeff_proxy_by_P[P]:> .12e}  {coeff_sum_by_P[P]:> .12e}  {float_total_by_P[P]:> .12e}"
            )
        return

    if args.boundary_pattern_report:
        if args.true_series:
            raise SystemExit("--boundary-pattern-report is only implemented for the surrogate normalization")

        pattern_scope = active_support if args.boundary_pattern_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in pattern_scope}

        pair_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        abs_coeff_proxy_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        coeff_sum_by_pattern: dict[tuple[int, int], float] = defaultdict(float)

        total_pairs = len(pattern_scope) * max(len(pattern_scope) - 1, 0)
        processed = 0
        started = time.time()
        for q in pattern_scope:
            cq = coeff_scope[q]
            for q2 in pattern_scope:
                if q == q2:
                    continue
                processed += 1
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                pair_count_by_pattern[pattern] += 1
                prod = cq * coeff_scope[q2]
                abs_coeff_proxy_by_pattern[pattern] += abs(prod)
                coeff_sum_by_pattern[pattern] += prod
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-pattern:pass1] processed={processed}/{total_pairs} "
                        f"patterns={len(pair_count_by_pattern)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        top_k = max(args.boundary_pattern_top, 1)
        top_patterns = sorted(
            pair_count_by_pattern.keys(),
            key=lambda pat: (abs_coeff_proxy_by_pattern[pat], pair_count_by_pattern[pat], -pat[0], -pat[1]),
            reverse=True,
        )[:top_k]
        top_pattern_set = set(top_patterns)

        q_needed: set[int] = set()
        for q in pattern_scope:
            for q2 in pattern_scope:
                if q == q2:
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                if pattern in top_pattern_set:
                    q_needed.add(q)
                    q_needed.add(q2)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        abs_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        g_signed_by_pattern: dict[tuple[int, int], dict[int, float]] = {
            pat: defaultdict(float) for pat in top_patterns
        }
        g_abs_by_pattern: dict[tuple[int, int], dict[int, float]] = {
            pat: defaultdict(float) for pat in top_patterns
        }

        processed = 0
        started = time.time()
        for q in pattern_scope:
            for q2 in pattern_scope:
                if q == q2:
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                if pattern not in top_pattern_set:
                    continue
                processed += 1
                val = surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
                signed_float_by_pattern[pattern] += val
                abs_float_by_pattern[pattern] += abs(val)
                g_signed_by_pattern[pattern][G] += val
                g_abs_by_pattern[pattern][G] += abs(val)
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-pattern:pass2] processed={processed} "
                        f"top_patterns={len(top_pattern_set)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        print("Surrogate boundary multiplier-pattern report")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_scope}")
        print(f"  support card              = {len(pattern_scope)}")
        print(f"  ordered offdiag pairs     = {total_pairs}")
        print(f"  distinct patterns         = {len(pair_count_by_pattern)}")
        print(f"  top patterns by abs coeff proxy = {top_k}")
        print()
        print("  pattern   pairs        abs coeff proxy      coeff sum proxy       signed float         abs float            ratio")
        for pattern in top_patterns:
            signed = signed_float_by_pattern[pattern]
            abs_mass = abs_float_by_pattern[pattern]
            ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
            print(
                f"  {pattern[0]}:{pattern[1]:<5} {pair_count_by_pattern[pattern]:>10}  "
                f"{abs_coeff_proxy_by_pattern[pattern]:> .12e}  {coeff_sum_by_pattern[pattern]:> .12e}  "
                f"{signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}"
            )
            top_gs = sorted(
                g_abs_by_pattern[pattern].keys(),
                key=lambda G: (g_abs_by_pattern[pattern][G], abs(g_signed_by_pattern[pattern][G]), -G),
                reverse=True,
            )[:max(args.boundary_pattern_top_g, 0)]
            for G in top_gs:
                gsigned = g_signed_by_pattern[pattern][G]
                gabs = g_abs_by_pattern[pattern][G]
                gratio = (abs(gsigned) / gabs) if gabs else 0.0
                print(
                    f"    G={G:<8d} signed={gsigned:> .12e}  abs={gabs:> .12e}  ratio={gratio:> .6f}"
                )
        return

    if args.boundary_pattern_g_report:
        if args.true_series:
            raise SystemExit("--boundary-pattern-g-report is only implemented for the surrogate normalization")

        block_scope = active_support if args.boundary_pattern_g_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in block_scope}

        pair_count_by_block: dict[tuple[tuple[int, int], int], int] = defaultdict(int)
        abs_coeff_proxy_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        coeff_sum_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)

        total_pairs = len(block_scope) * max(len(block_scope) - 1, 0)
        processed = 0
        started = time.time()
        for q in block_scope:
            cq = coeff_scope[q]
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                processed += 1
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                pair_count_by_block[block] += 1
                prod = cq * coeff_scope[q2]
                abs_coeff_proxy_by_block[block] += abs(prod)
                coeff_sum_by_block[block] += prod
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-pattern-g:pass1] processed={processed}/{total_pairs} "
                        f"blocks={len(pair_count_by_block)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        top_k = max(args.boundary_pattern_g_top, 1)
        candidate_k = (
            max(args.boundary_pattern_g_candidate_blocks, top_k)
            if args.boundary_pattern_g_candidate_blocks > 0
            else max(top_k * 10, top_k)
        )
        candidate_blocks = sorted(
            pair_count_by_block.keys(),
            key=lambda block: (
                abs_coeff_proxy_by_block[block],
                pair_count_by_block[block],
                -block[1],
                -block[0][0],
                -block[0][1],
            ),
            reverse=True,
        )[:candidate_k]
        top_block_set = set(candidate_blocks)

        q_needed: set[int] = set()
        for q in block_scope:
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block in top_block_set:
                    q_needed.add(q)
                    q_needed.add(q2)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        abs_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        top_pairs_by_block: dict[tuple[tuple[int, int], int], list[tuple[float, int, int, float]]] = {
            block: [] for block in candidate_blocks
        }

        processed = 0
        started = time.time()
        for q in block_scope:
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block not in top_block_set:
                    continue
                processed += 1
                val = surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
                signed_float_by_block[block] += val
                abs_float_by_block[block] += abs(val)
                pairs = top_pairs_by_block[block]
                pairs.append((abs(val), q, q2, val))
                if len(pairs) > max(args.boundary_pattern_g_top_pairs, 0):
                    pairs.sort(reverse=True)
                    del pairs[max(args.boundary_pattern_g_top_pairs, 0):]
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-pattern-g:pass2] processed={processed} "
                        f"top_blocks={len(top_block_set)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        top_blocks = sorted(
            candidate_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                abs(signed_float_by_block[block]),
                abs_coeff_proxy_by_block[block],
            ),
            reverse=True,
        )[:top_k]
        total_abs_over_candidates = math.fsum(abs_float_by_block[block] for block in candidate_blocks)

        print("Surrogate boundary multiplier-pattern-plus-G report")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_g_scope}")
        print(f"  support card              = {len(block_scope)}")
        print(f"  ordered offdiag pairs     = {total_pairs}")
        print(f"  distinct (pattern,G) blocks = {len(pair_count_by_block)}")
        print(f"  candidate blocks by abs coeff proxy = {candidate_k}")
        print(f"  final blocks by abs float = {top_k}")
        print(f"  total abs mass over evaluated candidates = {total_abs_over_candidates:.12e}")
        print()
        print("  pattern   G         pairs        abs coeff proxy      coeff sum proxy       signed float         abs float            ratio")
        for block in top_blocks:
            pattern, G = block
            signed = signed_float_by_block[block]
            abs_mass = abs_float_by_block[block]
            ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
            print(
                f"  {pattern[0]}:{pattern[1]:<5} {G:>8}  {pair_count_by_block[block]:>10}  "
                f"{abs_coeff_proxy_by_block[block]:> .12e}  {coeff_sum_by_block[block]:> .12e}  "
                f"{signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}"
            )
            if args.boundary_pattern_g_top_pairs > 0:
                for _, q, q2, val in sorted(top_pairs_by_block[block], reverse=True):
                    print(f"    pair=({q},{q2}) val={val:> .12e}")
        if args.boundary_pattern_g_cumulative:
            checkpoints = [10, 20, 30, 50, 100, 200, 500]
            print()
            print("Cumulative abs-mass share over evaluated candidate blocks")
            print("  N       top_abs_sum           share_of_candidate_abs")
            running = 0.0
            by_n: dict[int, float] = {}
            for i, block in enumerate(sorted(candidate_blocks, key=lambda b: abs_float_by_block[b], reverse=True), start=1):
                running += abs_float_by_block[block]
                if i in checkpoints:
                    by_n[i] = running
                if i >= max(checkpoints):
                    break
            for n in checkpoints:
                if n > len(candidate_blocks):
                    break
                top_abs = by_n.get(n, running)
                share = (top_abs / total_abs_over_candidates) if total_abs_over_candidates else 0.0
                print(f"  {n:>3}   {top_abs:> .12e}   {share:> .6f}")
        return

    if args.boundary_pattern_g_tail_report:
        if args.true_series:
            raise SystemExit("--boundary-pattern-g-tail-report is only implemented for the surrogate normalization")

        block_scope = active_support if args.boundary_pattern_g_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in block_scope}

        pair_count_by_block: dict[tuple[tuple[int, int], int], int] = defaultdict(int)
        abs_coeff_proxy_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        total_pairs = len(block_scope) * max(len(block_scope) - 1, 0)
        processed = 0
        started = time.time()
        for q in block_scope:
            cq = coeff_scope[q]
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                processed += 1
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                pair_count_by_block[block] += 1
                abs_coeff_proxy_by_block[block] += abs(cq * coeff_scope[q2])
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-pattern-tail:pass1] processed={processed}/{total_pairs} "
                        f"blocks={len(pair_count_by_block)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        top_k = max(args.boundary_pattern_g_remove_top, 0)
        candidate_k = (
            max(args.boundary_pattern_g_candidate_blocks, top_k, args.boundary_pattern_tail_top)
            if args.boundary_pattern_g_candidate_blocks > 0
            else max(max(top_k, args.boundary_pattern_tail_top) * 10, max(top_k, args.boundary_pattern_tail_top))
        )
        candidate_blocks = sorted(
            pair_count_by_block.keys(),
            key=lambda block: (
                abs_coeff_proxy_by_block[block],
                pair_count_by_block[block],
                -block[1],
                -block[0][0],
                -block[0][1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_block_set = set(candidate_blocks)

        q_needed: set[int] = set()
        for q in block_scope:
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block in candidate_block_set:
                    q_needed.add(q)
                    q_needed.add(q2)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        abs_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for q in block_scope:
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block not in candidate_block_set:
                    continue
                processed += 1
                val = surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
                signed_float_by_block[block] += val
                abs_float_by_block[block] += abs(val)
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-pattern-tail:pass2] processed={processed} "
                        f"candidate_blocks={len(candidate_block_set)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        ranked_blocks = sorted(
            candidate_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                abs(signed_float_by_block[block]),
                abs_coeff_proxy_by_block[block],
            ),
            reverse=True,
        )
        removed_blocks = set(ranked_blocks[:top_k])
        residual_signed_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        residual_abs_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        residual_block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        total_residual_abs = 0.0
        total_removed_abs = 0.0
        total_candidate_abs = 0.0
        for block in ranked_blocks:
            pattern, _ = block
            abs_mass = abs_float_by_block[block]
            signed = signed_float_by_block[block]
            total_candidate_abs += abs_mass
            if block in removed_blocks:
                total_removed_abs += abs_mass
            else:
                total_residual_abs += abs_mass
                residual_signed_by_pattern[pattern] += signed
                residual_abs_by_pattern[pattern] += abs_mass
                residual_block_count_by_pattern[pattern] += 1

        top_patterns = sorted(
            residual_abs_by_pattern.keys(),
            key=lambda pat: (
                residual_abs_by_pattern[pat],
                abs(residual_signed_by_pattern[pat]),
                residual_block_count_by_pattern[pat],
                -pat[0],
                -pat[1],
            ),
            reverse=True,
        )[:max(args.boundary_pattern_tail_top, 1)]

        print("Surrogate boundary residual pattern report after removing top (pattern,G) blocks")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_g_scope}")
        print(f"  support card              = {len(block_scope)}")
        print(f"  ordered offdiag pairs     = {total_pairs}")
        print(f"  candidate blocks evaluated = {len(candidate_blocks)}")
        print(f"  removed top blocks        = {top_k}")
        print(f"  candidate abs mass        = {total_candidate_abs:.12e}")
        print(f"  removed abs mass          = {total_removed_abs:.12e}")
        print(f"  residual abs mass         = {total_residual_abs:.12e}")
        print()
        print("  residual pattern   signed               abs                  ratio       residual block count")
        for pat in top_patterns:
            signed = residual_signed_by_pattern[pat]
            abs_mass = residual_abs_by_pattern[pat]
            ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
            print(
                f"  {pat[0]}:{pat[1]:<7} {signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}  {residual_block_count_by_pattern[pat]:>10}"
            )
        return

    if args.boundary_pattern_family_detail is not None:
        if args.true_series:
            raise SystemExit("--boundary-pattern-family-detail is only implemented for the surrogate normalization")

        a, b = args.boundary_pattern_family_detail
        if a <= 0 or b <= 0:
            raise SystemExit("pattern entries must be positive")
        target_pattern = (a, b) if a <= b else (b, a)
        family_scope = active_support if args.boundary_pattern_family_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in family_scope}

        pair_count_by_block: dict[tuple[tuple[int, int], int], int] = defaultdict(int)
        abs_coeff_proxy_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        total_pairs = len(family_scope) * max(len(family_scope) - 1, 0)
        processed = 0
        started = time.time()
        for q in family_scope:
            cq = coeff_scope[q]
            for q2 in family_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                processed += 1
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                pair_count_by_block[block] += 1
                abs_coeff_proxy_by_block[block] += abs(cq * coeff_scope[q2])
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-pattern-family:pass1] processed={processed}/{total_pairs} "
                        f"blocks={len(pair_count_by_block)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        remove_top = max(args.boundary_pattern_g_remove_top, 0)
        candidate_k = (
            max(args.boundary_pattern_g_candidate_blocks, remove_top, args.boundary_pattern_family_top_g)
            if args.boundary_pattern_g_candidate_blocks > 0
            else max(max(remove_top, args.boundary_pattern_family_top_g) * 10, max(remove_top, args.boundary_pattern_family_top_g))
        )
        candidate_blocks = sorted(
            pair_count_by_block.keys(),
            key=lambda block: (
                abs_coeff_proxy_by_block[block],
                pair_count_by_block[block],
                -block[1],
                -block[0][0],
                -block[0][1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_block_set = set(candidate_blocks)

        q_needed: set[int] = set()
        for q in family_scope:
            for q2 in family_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block in candidate_block_set:
                    q_needed.add(q)
                    q_needed.add(q2)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        abs_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for q in family_scope:
            for q2 in family_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block not in candidate_block_set:
                    continue
                processed += 1
                val = surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
                signed_float_by_block[block] += val
                abs_float_by_block[block] += abs(val)
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-pattern-family:pass2] processed={processed} "
                        f"candidate_blocks={len(candidate_block_set)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        ranked_blocks = sorted(
            candidate_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                abs(signed_float_by_block[block]),
                abs_coeff_proxy_by_block[block],
            ),
            reverse=True,
        )
        removed_blocks = set(ranked_blocks[:remove_top])

        family_blocks: list[tuple[tuple[int, int], int]] = []
        family_signed_total = 0.0
        family_abs_total = 0.0
        for block in ranked_blocks:
            pattern, _ = block
            if block in removed_blocks or pattern != target_pattern:
                continue
            family_blocks.append(block)
            family_signed_total += signed_float_by_block[block]
            family_abs_total += abs_float_by_block[block]

        top_family_blocks = sorted(
            family_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                abs(signed_float_by_block[block]),
                block[1],
            ),
            reverse=True,
        )[:max(args.boundary_pattern_family_top_g, 1)]

        print("Surrogate boundary residual family detail")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_family_scope}")
        print(f"  target pattern            = {target_pattern[0]}:{target_pattern[1]}")
        print(f"  candidate blocks evaluated = {len(candidate_blocks)}")
        print(f"  removed top blocks        = {remove_top}")
        print(f"  family block count        = {len(family_blocks)}")
        print(f"  family signed total       = {family_signed_total:.12e}")
        print(f"  family abs total          = {family_abs_total:.12e}")
        ratio = (abs(family_signed_total) / family_abs_total) if family_abs_total else 0.0
        print(f"  family ratio              = {ratio:.6f}")
        print()
        print("  G         pairs        signed float         abs float            ratio")
        running_abs = 0.0
        checkpoints = [5, 10, 20, 50]
        by_n: dict[int, float] = {}
        for i, block in enumerate(top_family_blocks, start=1):
            _, G = block
            signed = signed_float_by_block[block]
            abs_mass = abs_float_by_block[block]
            block_ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
            print(
                f"  {G:>8}  {pair_count_by_block[block]:>10}  {signed:> .12e}  {abs_mass:> .12e}  {block_ratio:> .6f}"
            )
            running_abs += abs_mass
            if i in checkpoints:
                by_n[i] = running_abs

        if args.boundary_pattern_family_cumulative:
            print()
            print("Cumulative abs-mass share by top G-values")
            print("  N       top_abs_sum           share_of_family_abs")
            for n in checkpoints:
                if n > len(top_family_blocks):
                    break
                top_abs = by_n.get(n, running_abs)
                share = (top_abs / family_abs_total) if family_abs_total else 0.0
                print(f"  {n:>3}   {top_abs:> .12e}   {share:> .6f}")
            shown_abs = math.fsum(abs_float_by_block[block] for block in top_family_blocks)
            tail_abs = family_abs_total - shown_abs
            print(f"  tail  {tail_abs:> .12e}")
        return

    if args.boundary_pattern_family_exact is not None:
        if args.true_series:
            raise SystemExit("--boundary-pattern-family-exact is only implemented for the surrogate normalization")

        a, b = args.boundary_pattern_family_exact
        if a <= 0 or b <= 0:
            raise SystemExit("pattern entries must be positive")
        target_pattern = (a, b) if a <= b else (b, a)
        family_scope = active_support if args.boundary_pattern_family_scope == "active" else support

        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            family_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )
        family_result = evaluate_exact_boundary_pattern_family(
            X=X,
            target_pattern=target_pattern,
            family_scope=family_scope,
            pair_count_by_block=pair_count_by_block,
            total_pairs=total_pairs,
            mu=mu,
            phi=phi,
            spf=spf,
            even_window_card=even_window_card,
            progress=args.progress,
            progress_every=args.progress_every,
        )
        family_blocks = family_result["family_blocks"]
        family_signed = family_result["signed"]
        family_abs = family_result["abs"]
        elapsed_by_block = family_result["elapsed_by_block"]
        signed_by_block = family_result["signed_by_block"]
        abs_by_block = family_result["abs_by_block"]
        g_prime_support_signed = family_result["g_prime_support_signed"]
        g_prime_support_abs = family_result["g_prime_support_abs"]
        g_prime_support_count = family_result["g_prime_support_count"]
        total_elapsed = float(family_result["elapsed_sec"])

        top_g_blocks = sorted(
            family_blocks,
            key=lambda block: (elapsed_by_block[block], float(abs_by_block[block]), block[1]),
            reverse=True,
        )[:max(args.boundary_pattern_family_top_g, 1)]
        top_prime_supports = sorted(
            g_prime_support_count.keys(),
            key=lambda sig: (g_prime_support_count[sig], float(g_prime_support_abs[sig]), sig),
            reverse=True,
        )[:max(args.boundary_pattern_family_top_g, 1)]

        ratio = (abs(float(family_signed)) / float(family_abs)) if family_abs else 0.0
        print("Active boundary exact family report")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_family_scope}")
        print(f"  target pattern            = {target_pattern[0]}:{target_pattern[1]}")
        print(f"  support card              = {len(family_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  G-value count             = {family_result['g_count']}")
        print(f"  pair mass                 = {family_result['pair_mass']}")
        print(f"  exact signed total        = {float(family_signed):.12e}")
        print(f"  exact abs total           = {float(family_abs):.12e}")
        print(f"  family ratio              = {ratio:.6f}")
        print(f"  elapsed sec               = {total_elapsed:.3f}")
        print(f"  avg ms/G                  = {1000.0 * total_elapsed / len(family_blocks):.3f}")
        print(f"  Lean ℚ signed             = {fraction_to_q_literal(family_signed)}")
        print()
        print("  slowest G-values")
        print("  G         pair_mass   elapsed_ms    signed               abs")
        for block in top_g_blocks:
            _, G = block
            print(
                f"  {G:>8}  {pair_count_by_block[block]:>9}  {1000.0 * elapsed_by_block[block]:>10.3f}  "
                f"{float(signed_by_block[block]):> .12e}  {float(abs_by_block[block]):> .12e}"
            )
        print()
        print("  prime-support classes")
        print("  support                 G-count    signed               abs")
        for sig in top_prime_supports:
            print(
                f"  {sig!r:<22} {g_prime_support_count[sig]:>7}  "
                f"{float(g_prime_support_signed[sig]):> .12e}  {float(g_prime_support_abs[sig]):> .12e}"
            )
        return

    if args.boundary_pattern_family_exact_batch:
        if args.true_series:
            raise SystemExit("--boundary-pattern-family-exact-batch is only implemented for the surrogate normalization")

        target_patterns = sorted(parse_selected_patterns(args.boundary_pattern_family_exact_batch))
        family_scope = active_support if args.boundary_pattern_family_scope == "active" else support
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            family_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        results: list[dict[str, object]] = []
        combined_signed = Fraction(0, 1)
        combined_abs = Fraction(0, 1)
        total_elapsed = 0.0
        for pattern in target_patterns:
            result = evaluate_exact_boundary_pattern_family(
                X=X,
                target_pattern=pattern,
                family_scope=family_scope,
                pair_count_by_block=pair_count_by_block,
                total_pairs=total_pairs,
                mu=mu,
                phi=phi,
                spf=spf,
                even_window_card=even_window_card,
                progress=args.progress,
                progress_every=args.progress_every,
            )
            results.append(result)
            combined_signed += result["signed"]
            combined_abs += result["abs"]
            total_elapsed += float(result["elapsed_sec"])

        print("Active boundary exact family batch report")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_family_scope}")
        print(f"  support card              = {len(family_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  family count              = {len(results)}")
        print(f"  combined exact signed     = {float(combined_signed):.12e}")
        print(f"  combined exact abs        = {float(combined_abs):.12e}")
        print(f"  combined ratio            = {(abs(float(combined_signed)) / float(combined_abs)) if combined_abs else 0.0:.6f}")
        print(f"  combined elapsed sec      = {total_elapsed:.3f}")
        print(f"  Lean ℚ combined signed    = {fraction_to_q_literal(combined_signed)}")
        print()
        print("  pattern   G-count   pair mass     exact signed         exact abs            ratio     elapsed sec   avg ms/G")
        for result in results:
            pattern = result["pattern"]
            signed = result["signed"]
            abs_mass = result["abs"]
            elapsed_sec = float(result["elapsed_sec"])
            g_count = int(result["g_count"])
            ratio = (abs(float(signed)) / float(abs_mass)) if abs_mass else 0.0
            print(
                f"  {pattern[0]}:{pattern[1]:<5} {g_count:>8}  {int(result['pair_mass']):>10}  "
                f"{float(signed):> .12e}  {float(abs_mass):> .12e}  {ratio:> .6f}  "
                f"{elapsed_sec:>11.3f}  {1000.0 * elapsed_sec / max(g_count, 1):>9.3f}"
            )
        return

    if args.boundary_selected_block_certificate_report:
        if args.true_series:
            raise SystemExit("--boundary-selected-block-certificate-report is only implemented for the surrogate normalization")

        selected_patterns: set[tuple[int, int]] = set()
        for raw in args.boundary_family_patterns:
            if ":" not in raw:
                raise SystemExit(f"invalid pattern {raw!r}; expected m:n")
            left, right = raw.split(":", 1)
            m = int(left)
            n = int(right)
            if m <= 0 or n <= 0:
                raise SystemExit(f"invalid pattern {raw!r}; entries must be positive")
            selected_patterns.add((m, n) if m <= n else (n, m))

        block_scope = active_support if args.boundary_pattern_g_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in block_scope}

        pair_count_by_block: dict[tuple[tuple[int, int], int], int] = defaultdict(int)
        abs_coeff_proxy_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        total_pairs = len(block_scope) * max(len(block_scope) - 1, 0)
        processed = 0
        started = time.time()
        for q in block_scope:
            cq = coeff_scope[q]
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                processed += 1
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                pair_count_by_block[block] += 1
                abs_coeff_proxy_by_block[block] += abs(cq * coeff_scope[q2])
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-selected:pass1] processed={processed}/{total_pairs} "
                        f"blocks={len(pair_count_by_block)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        top_remove = max(args.boundary_pattern_g_remove_top, 0)
        candidate_k = (
            max(args.boundary_pattern_g_candidate_blocks, top_remove, args.boundary_selected_leftover_top)
            if args.boundary_pattern_g_candidate_blocks > 0
            else max(max(top_remove, args.boundary_selected_leftover_top) * 10, max(top_remove, args.boundary_selected_leftover_top))
        )
        candidate_blocks = sorted(
            pair_count_by_block.keys(),
            key=lambda block: (
                abs_coeff_proxy_by_block[block],
                pair_count_by_block[block],
                -block[1],
                -block[0][0],
                -block[0][1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_block_set = set(candidate_blocks)

        q_needed: set[int] = set()
        for q in block_scope:
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block in candidate_block_set:
                    q_needed.add(q)
                    q_needed.add(q2)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        abs_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for q in block_scope:
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block not in candidate_block_set:
                    continue
                processed += 1
                val = surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
                signed_float_by_block[block] += val
                abs_float_by_block[block] += abs(val)
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[boundary-selected:pass2] processed={processed} "
                        f"candidate_blocks={len(candidate_block_set)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        ranked_blocks = sorted(
            candidate_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                abs(signed_float_by_block[block]),
                abs_coeff_proxy_by_block[block],
            ),
            reverse=True,
        )
        top_global_blocks = set(ranked_blocks[:top_remove])
        expanded_family_blocks = {
            block for block in ranked_blocks[top_remove:]
            if block[0] in selected_patterns
        }
        selected_blocks = top_global_blocks | expanded_family_blocks

        selected_signed = 0.0
        selected_abs = 0.0
        leftover_signed = 0.0
        leftover_abs = 0.0
        coherent_leftover_signed = 0.0
        coherent_leftover_abs = 0.0
        coherent_leftover_blocks = 0
        incoherent_leftover_signed = 0.0
        incoherent_leftover_abs = 0.0
        incoherent_leftover_blocks = 0
        leftover_signed_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        leftover_abs_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        leftover_block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        total_candidate_signed = 0.0
        total_candidate_abs = 0.0
        coherent_threshold = 1.0 - 1e-12
        for block in ranked_blocks:
            signed = signed_float_by_block[block]
            abs_mass = abs_float_by_block[block]
            pattern, _ = block
            ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
            total_candidate_signed += signed
            total_candidate_abs += abs_mass
            if block in selected_blocks:
                selected_signed += signed
                selected_abs += abs_mass
            else:
                leftover_signed += signed
                leftover_abs += abs_mass
                if pair_count_by_block[block] == 2 and ratio >= coherent_threshold:
                    coherent_leftover_signed += signed
                    coherent_leftover_abs += abs_mass
                    coherent_leftover_blocks += 1
                else:
                    incoherent_leftover_signed += signed
                    incoherent_leftover_abs += abs_mass
                    incoherent_leftover_blocks += 1
                leftover_signed_by_pattern[pattern] += signed
                leftover_abs_by_pattern[pattern] += abs_mass
                leftover_block_count_by_pattern[pattern] += 1

        top_leftover_patterns = sorted(
            leftover_abs_by_pattern.keys(),
            key=lambda pat: (
                leftover_abs_by_pattern[pat],
                abs(leftover_signed_by_pattern[pat]),
                leftover_block_count_by_pattern[pat],
                -pat[0],
                -pat[1],
            ),
            reverse=True,
        )[:max(args.boundary_selected_leftover_top, 1)]

        print("Surrogate boundary selected-block certificate report")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_g_scope}")
        print(f"  candidate blocks evaluated = {len(candidate_blocks)}")
        print(f"  top global blocks selected = {len(top_global_blocks)}")
        print(f"  expanded family patterns   = {sorted(selected_patterns)}")
        print(f"  expanded family blocks     = {len(expanded_family_blocks)}")
        print(f"  total selected blocks      = {len(selected_blocks)}")
        print(f"  candidate signed total     = {total_candidate_signed:.12e}")
        print(f"  candidate abs total        = {total_candidate_abs:.12e}")
        print(f"  selected signed total      = {selected_signed:.12e}")
        print(f"  selected abs total         = {selected_abs:.12e}")
        print(f"  leftover signed total      = {leftover_signed:.12e}")
        print(f"  leftover abs total         = {leftover_abs:.12e}")
        selected_share = (selected_abs / total_candidate_abs) if total_candidate_abs else 0.0
        leftover_share = (leftover_abs / total_candidate_abs) if total_candidate_abs else 0.0
        print(f"  selected abs share         = {selected_share:.6f}")
        print(f"  leftover abs share         = {leftover_share:.6f}")
        print()
        print("  selected/coherent-pair2/incoherent split over evaluated candidate blocks")
        for label, signed, abs_mass, count in [
            ("selected", selected_signed, selected_abs, len(selected_blocks)),
            ("coherent_pair2_leftover", coherent_leftover_signed, coherent_leftover_abs, coherent_leftover_blocks),
            ("incoherent_leftover", incoherent_leftover_signed, incoherent_leftover_abs, incoherent_leftover_blocks),
        ]:
            ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
            share = (abs_mass / total_candidate_abs) if total_candidate_abs else 0.0
            print(
                f"    {label:<24} signed={signed:> .12e}  abs={abs_mass:> .12e}  "
                f"ratio={ratio:> .6f}  blocks={count:>6}  share={share:> .6f}"
            )
        print()
        print("  top leftover pattern   signed               abs                  ratio       leftover block count")
        for pat in top_leftover_patterns:
            signed = leftover_signed_by_pattern[pat]
            abs_mass = leftover_abs_by_pattern[pat]
            ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
            print(
                f"  {pat[0]}:{pat[1]:<7} {signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}  {leftover_block_count_by_pattern[pat]:>10}"
            )
        if args.boundary_selected_coherence_report:
            coherence_by_pair_count: dict[int, dict[str, float]] = defaultdict(lambda: {
                "coherent_abs": 0.0,
                "incoherent_abs": 0.0,
                "coherent_count": 0.0,
                "incoherent_count": 0.0,
            })
            for block in ranked_blocks:
                if block in selected_blocks:
                    continue
                pairs = pair_count_by_block[block]
                signed = signed_float_by_block[block]
                abs_mass = abs_float_by_block[block]
                ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
                bucket = coherence_by_pair_count[pairs]
                if ratio >= coherent_threshold:
                    bucket["coherent_abs"] += abs_mass
                    bucket["coherent_count"] += 1.0
                else:
                    bucket["incoherent_abs"] += abs_mass
                    bucket["incoherent_count"] += 1.0
            print()
            print("  leftover block-count/coherence summary")
            print("  pairs    coherent_abs        incoherent_abs      coherent_blocks   incoherent_blocks")
            for pairs in sorted(coherence_by_pair_count):
                bucket = coherence_by_pair_count[pairs]
                print(
                    f"  {pairs:>5}   {bucket['coherent_abs']:> .12e}  {bucket['incoherent_abs']:> .12e}  "
                    f"{int(bucket['coherent_count']):>14}  {int(bucket['incoherent_count']):>16}"
                )
        if args.emit_boundary_selected_rat_certificate:
            q_needed_exact: set[int] = set()
            for pattern, G in candidate_blocks:
                m, n = pattern
                q_needed_exact.add(G * m)
                q_needed_exact.add(G * n)
            exact_ctx = build_surrogate_boundary_exact_context(
                X, mu, phi, spf, even_window_card, sorted(q_needed_exact),
                progress=args.progress,
            )
            selected_rat = Fraction(0, 1)
            coherent_pair2_rat = Fraction(0, 1)
            incoherent_rat = Fraction(0, 1)
            coherent_leftover_block_set = {
                block for block in ranked_blocks
                if block not in selected_blocks
                and pair_count_by_block[block] == 2
                and ((abs(signed_float_by_block[block]) / abs_float_by_block[block]) if abs_float_by_block[block] else 0.0) >= coherent_threshold
            }
            incoherent_block_set = {
                block for block in ranked_blocks
                if block not in selected_blocks and block not in coherent_leftover_block_set
            }
            processed_exact = 0
            started_exact = time.time()
            for block in ranked_blocks:
                pattern, G = block
                m, n = pattern
                q = G * m
                q2 = G * n
                if pair_count_by_block[block] != 2:
                    raise RuntimeError(
                        f"expected pair-count-2 (pattern,G) block, got {pair_count_by_block[block]} for {block}"
                    )
                processed_exact += 1
                # `(pattern,G)` is an unordered reversible block, so the two ordered-pair contributions
                # are the forward term and its swap. The surrogate boundary summand is symmetric in
                # `(q,q2)`, so evaluate once and double instead of recomputing the swapped term.
                block_term = 2 * surrogate_boundary_pair_contribution_rat_cached(X, q, q2, exact_ctx)
                if block in selected_blocks:
                    selected_rat += block_term
                elif block in coherent_leftover_block_set:
                    coherent_pair2_rat += block_term
                elif block in incoherent_block_set:
                    incoherent_rat += block_term
                if args.progress and processed_exact % args.progress_every == 0:
                    elapsed = time.time() - started_exact
                    print(
                        f"[boundary-selected:exact] processed_blocks={processed_exact}/{len(ranked_blocks)} "
                        f"elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )
            print()
            print("  exact rational totals over evaluated candidate blocks")
            print(f"    selected_exact_num = {selected_rat.numerator}")
            print(f"    selected_exact_den = {selected_rat.denominator}")
            print(f"    selected_exact_q   = {fraction_to_q_literal(selected_rat)}")
            print(f"    coherent_pair2_num = {coherent_pair2_rat.numerator}")
            print(f"    coherent_pair2_den = {coherent_pair2_rat.denominator}")
            print(f"    coherent_pair2_q   = {fraction_to_q_literal(coherent_pair2_rat)}")
            print(f"    incoherent_num     = {incoherent_rat.numerator}")
            print(f"    incoherent_den     = {incoherent_rat.denominator}")
            print(f"    incoherent_q       = {fraction_to_q_literal(incoherent_rat)}")
        return

    if args.coh2_formula_audit:
        if args.true_series:
            raise SystemExit("--coh2-formula-audit is only implemented for the surrogate normalization")

        selected_patterns: set[tuple[int, int]] = set()
        for raw in args.boundary_family_patterns:
            if ":" not in raw:
                raise SystemExit(f"invalid pattern {raw!r}; expected m:n")
            left, right = raw.split(":", 1)
            m = int(left)
            n = int(right)
            if m <= 0 or n <= 0:
                raise SystemExit(f"invalid pattern {raw!r}; entries must be positive")
            selected_patterns.add((m, n) if m <= n else (n, m))

        block_scope = active_support if args.boundary_pattern_g_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in block_scope}

        pair_count_by_block: dict[tuple[tuple[int, int], int], int] = defaultdict(int)
        abs_coeff_proxy_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        total_pairs = len(block_scope) * max(len(block_scope) - 1, 0)
        processed = 0
        started = time.time()
        for q in block_scope:
            cq = coeff_scope[q]
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                processed += 1
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                pair_count_by_block[block] += 1
                abs_coeff_proxy_by_block[block] += abs(cq * coeff_scope[q2])
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[coh2-formula:pass1] processed={processed}/{total_pairs} "
                        f"blocks={len(pair_count_by_block)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        top_remove = max(args.boundary_pattern_g_remove_top, 0)
        candidate_k = (
            max(args.boundary_pattern_g_candidate_blocks, top_remove, args.coh2_formula_top)
            if args.boundary_pattern_g_candidate_blocks > 0
            else max(max(top_remove, args.coh2_formula_top) * 10, max(top_remove, args.coh2_formula_top))
        )
        candidate_blocks = sorted(
            pair_count_by_block.keys(),
            key=lambda block: (
                abs_coeff_proxy_by_block[block],
                pair_count_by_block[block],
                -block[1],
                -block[0][0],
                -block[0][1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_block_set = set(candidate_blocks)

        q_needed: set[int] = set()
        for pattern, G in candidate_blocks:
            m, n = pattern
            q_needed.add(G * m)
            q_needed.add(G * n)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        abs_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for q in block_scope:
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block not in candidate_block_set:
                    continue
                processed += 1
                val = surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
                signed_float_by_block[block] += val
                abs_float_by_block[block] += abs(val)
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[coh2-formula:pass2] processed={processed} "
                        f"candidate_blocks={len(candidate_block_set)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        ranked_blocks = sorted(
            candidate_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                abs(signed_float_by_block[block]),
                abs_coeff_proxy_by_block[block],
            ),
            reverse=True,
        )
        top_global_blocks = set(ranked_blocks[:top_remove])
        expanded_family_blocks = {
            block for block in ranked_blocks[top_remove:]
            if block[0] in selected_patterns
        }
        selected_blocks = top_global_blocks | expanded_family_blocks
        coherent_threshold = 1.0 - 1e-12
        coherent_leftover_blocks = [
            block for block in ranked_blocks
            if block not in selected_blocks
            and pair_count_by_block[block] == 2
            and ((abs(signed_float_by_block[block]) / abs_float_by_block[block]) if abs_float_by_block[block] else 0.0) >= coherent_threshold
        ]
        incoherent_leftover_blocks = [
            block for block in ranked_blocks
            if block not in selected_blocks and block not in coherent_leftover_blocks
        ]

        sum_abs_gcd_coeff_cache: dict[int, int] = {}

        def sum_abs_gcd_coeff(q: int) -> int:
            if q not in sum_abs_gcd_coeff_cache:
                sum_abs_gcd_coeff_cache[q] = sum_abs_ramanujan_gcd_class_coeff(q, mu, phi, spf)
            return sum_abs_gcd_coeff_cache[q]

        majorant_by_block: dict[tuple[tuple[int, int], int], float] = {}
        coherent_abs_total = 0.0
        coherent_majorant_total = 0.0
        coherent_signed_total = 0.0
        for block in coherent_leftover_blocks:
            pattern, G = block
            m, n = pattern
            q = G * m
            q2 = G * n
            coeff_prod = abs(coeff_scope[q] * coeff_scope[q2])
            even_count = boundary_remainder_even_count(X, q, q2)
            sum_abs_q = sum_abs_gcd_coeff(q)
            sum_abs_q2 = sum_abs_gcd_coeff(q2)
            block_majorant = 2.0 * coeff_prod * even_count * float(sum_abs_q * sum_abs_q2)
            majorant_by_block[block] = block_majorant
            coherent_abs_total += abs_float_by_block[block]
            coherent_majorant_total += block_majorant
            coherent_signed_total += signed_float_by_block[block]

        top_blocks = sorted(
            coherent_leftover_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                majorant_by_block[block],
                block[1],
                block[0][0],
                block[0][1],
            ),
            reverse=True,
        )[:max(args.coh2_formula_top, 1)]

        incoherent_abs_total = math.fsum(abs_float_by_block[block] for block in incoherent_leftover_blocks)
        incoherent_signed_total = math.fsum(signed_float_by_block[block] for block in incoherent_leftover_blocks)

        print("Surrogate coherent pair-count-2 boundary formula audit")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_g_scope}")
        print(f"  candidate blocks evaluated = {len(candidate_blocks)}")
        print(f"  top global blocks selected = {len(top_global_blocks)}")
        print(f"  expanded family patterns   = {sorted(selected_patterns)}")
        print(f"  expanded family blocks     = {len(expanded_family_blocks)}")
        print(f"  coherent pair-count-2 leftover blocks = {len(coherent_leftover_blocks)}")
        print(f"  incoherent leftover blocks  = {len(incoherent_leftover_blocks)}")
        print(f"  coherent signed total      = {coherent_signed_total:.12e}")
        print(f"  coherent abs total         = {coherent_abs_total:.12e}")
        print(f"  coherent majorant total    = {coherent_majorant_total:.12e}")
        coh_ratio = (coherent_abs_total / coherent_majorant_total) if coherent_majorant_total else 0.0
        print(f"  coherent abs / majorant    = {coh_ratio:.6f}")
        print(f"  incoherent signed total    = {incoherent_signed_total:.12e}")
        print(f"  incoherent abs total       = {incoherent_abs_total:.12e}")
        print()
        print("  pattern   G         q      q'      P        r_even   block_abs            majorant             abs/maj   coeff_prod         sumAbs(q)  sumAbs(q')")
        for block in top_blocks:
            pattern, G = block
            m, n = pattern
            q = G * m
            q2 = G * n
            P = block_period(q, q2)
            r_even = boundary_remainder_even_count(X, q, q2)
            coeff_prod = abs(coeff_scope[q] * coeff_scope[q2])
            sum_abs_q = sum_abs_gcd_coeff(q)
            sum_abs_q2 = sum_abs_gcd_coeff(q2)
            abs_mass = abs_float_by_block[block]
            maj = majorant_by_block[block]
            ratio = (abs_mass / maj) if maj else 0.0
            print(
                f"  {pattern[0]}:{pattern[1]:<5} {G:>8}  {q:>6}  {q2:>6}  {P:>7}  {r_even:>7}  "
                f"{abs_mass:> .12e}  {maj:> .12e}  {ratio:> .6f}  {coeff_prod:> .12e}  {sum_abs_q:>9}  {sum_abs_q2:>9}"
            )
        return

    if args.coh2_centered_core_audit:
        if args.true_series:
            raise SystemExit("--coh2-centered-core-audit is only implemented for the surrogate normalization")

        selected_patterns: set[tuple[int, int]] = set()
        for raw in args.boundary_family_patterns:
            if ":" not in raw:
                raise SystemExit(f"invalid pattern {raw!r}; expected m:n")
            left, right = raw.split(":", 1)
            m = int(left)
            n = int(right)
            if m <= 0 or n <= 0:
                raise SystemExit(f"invalid pattern {raw!r}; entries must be positive")
            selected_patterns.add((m, n) if m <= n else (n, m))

        block_scope = active_support if args.boundary_pattern_g_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in block_scope}

        pair_count_by_block: dict[tuple[tuple[int, int], int], int] = defaultdict(int)
        abs_coeff_proxy_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        total_pairs = len(block_scope) * max(len(block_scope) - 1, 0)
        processed = 0
        started = time.time()
        for q in block_scope:
            cq = coeff_scope[q]
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                processed += 1
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                pair_count_by_block[block] += 1
                abs_coeff_proxy_by_block[block] += abs(cq * coeff_scope[q2])
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[coh2-core:pass1] processed={processed}/{total_pairs} "
                        f"blocks={len(pair_count_by_block)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        top_remove = max(args.boundary_pattern_g_remove_top, 0)
        candidate_k = (
            max(args.boundary_pattern_g_candidate_blocks, top_remove, args.coh2_formula_top)
            if args.boundary_pattern_g_candidate_blocks > 0
            else max(max(top_remove, args.coh2_formula_top) * 10, max(top_remove, args.coh2_formula_top))
        )
        candidate_blocks = sorted(
            pair_count_by_block.keys(),
            key=lambda block: (
                abs_coeff_proxy_by_block[block],
                pair_count_by_block[block],
                -block[1],
                -block[0][0],
                -block[0][1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_block_set = set(candidate_blocks)

        q_needed: set[int] = set()
        for pattern, G in candidate_blocks:
            m, n = pattern
            q_needed.add(G * m)
            q_needed.add(G * n)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        abs_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for q in block_scope:
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block not in candidate_block_set:
                    continue
                processed += 1
                val = surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
                signed_float_by_block[block] += val
                abs_float_by_block[block] += abs(val)
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[coh2-core:pass2] processed={processed} "
                        f"candidate_blocks={len(candidate_block_set)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        ranked_blocks = sorted(
            candidate_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                abs(signed_float_by_block[block]),
                abs_coeff_proxy_by_block[block],
            ),
            reverse=True,
        )
        top_global_blocks = set(ranked_blocks[:top_remove])
        expanded_family_blocks = {
            block for block in ranked_blocks[top_remove:]
            if block[0] in selected_patterns
        }
        selected_blocks = top_global_blocks | expanded_family_blocks
        coherent_threshold = 1.0 - 1e-12
        coherent_leftover_blocks = [
            block for block in ranked_blocks
            if block not in selected_blocks
            and pair_count_by_block[block] == 2
            and ((abs(signed_float_by_block[block]) / abs_float_by_block[block]) if abs_float_by_block[block] else 0.0) >= coherent_threshold
        ]
        incoherent_leftover_blocks = [
            block for block in ranked_blocks
            if block not in selected_blocks and block not in coherent_leftover_blocks
        ]

        crude_majorant_total = 0.0
        centered_majorant_total = 0.0
        coherent_abs_total = 0.0
        coherent_signed_total = 0.0
        for block in coherent_leftover_blocks:
            pattern, G = block
            m, n = pattern
            q = G * m
            q2 = G * n
            coeff_prod = abs(coeff_scope[q] * coeff_scope[q2])
            core, core_abs, _ = centered_boundary_core_float_detail(X, q, q2, ctx)
            crude_majorant_total += 2.0 * coeff_prod * core_abs
            centered_majorant_total += 2.0 * coeff_prod * abs(core)
            coherent_abs_total += abs_float_by_block[block]
            coherent_signed_total += signed_float_by_block[block]

        selected_signed_total = math.fsum(signed_float_by_block[block] for block in selected_blocks)
        selected_abs_signed = abs(selected_signed_total)
        incoherent_signed_total = math.fsum(signed_float_by_block[block] for block in incoherent_leftover_blocks)
        incoherent_abs_signed = abs(incoherent_signed_total)
        exact_boundary_signed_total = (
            selected_signed_total + coherent_signed_total + incoherent_signed_total
        )
        structural_bound_total = (
            selected_abs_signed + centered_majorant_total + incoherent_abs_signed
        )

        top_blocks = sorted(
            coherent_leftover_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                block[1],
                block[0][0],
                block[0][1],
            ),
            reverse=True,
        )[:max(args.coh2_formula_top, 1)]

        print("Surrogate coherent pair-count-2 centered-core audit")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_g_scope}")
        print(f"  candidate blocks evaluated = {len(candidate_blocks)}")
        print(f"  top global blocks selected = {len(top_global_blocks)}")
        print(f"  expanded family patterns   = {sorted(selected_patterns)}")
        print(f"  expanded family blocks     = {len(expanded_family_blocks)}")
        print(f"  coherent pair-count-2 leftover blocks = {len(coherent_leftover_blocks)}")
        print(f"  coherent abs total         = {coherent_abs_total:.12e}")
        print(f"  crude gh abs majorant total = {crude_majorant_total:.12e}")
        print(f"  centered-core majorant total = {centered_majorant_total:.12e}")
        print(f"  coherent abs / crude total = {(coherent_abs_total / crude_majorant_total) if crude_majorant_total else 0.0:.6f}")
        print(f"  coherent abs / centered total = {(coherent_abs_total / centered_majorant_total) if centered_majorant_total else 0.0:.6f}")
        print()
        print("  theorem-facing structural table over evaluated candidate blocks")
        print(f"  selected_signed           = {selected_signed_total:.12e}")
        print(f"  abs_selected              = {selected_abs_signed:.12e}")
        print(f"  coh2_signed               = {coherent_signed_total:.12e}")
        print(f"  coh2_centered_majorant    = {centered_majorant_total:.12e}")
        print(f"  incoh_signed              = {incoherent_signed_total:.12e}")
        print(f"  abs_incoh                 = {incoherent_abs_signed:.12e}")
        print(f"  exact_boundary_signed     = {exact_boundary_signed_total:.12e}")
        print(f"  structural_bound_total    = {structural_bound_total:.12e}")
        print(f"  target_decimal_lhs        = {abs(boundary_total):.12e}")
        print(f"  target_26                 = {26.0:.12e}")
        print()
        print("  pattern   G         q      q'      block_abs            crude_gh_abs_maj      centered_core_abs    abs/crude")
        for block in top_blocks:
            pattern, G = block
            m, n = pattern
            q = G * m
            q2 = G * n
            coeff_prod = abs(coeff_scope[q] * coeff_scope[q2])
            block_abs = abs_float_by_block[block]
            core, core_abs, detail = centered_boundary_core_float_detail(X, q, q2, ctx)
            crude_gh_abs_majorant = 2.0 * coeff_prod * core_abs
            centered_core_majorant = 2.0 * coeff_prod * abs(core)
            ratio_crude = (block_abs / crude_gh_abs_majorant) if crude_gh_abs_majorant else 0.0
            ratio_centered = (block_abs / centered_core_majorant) if centered_core_majorant else 0.0
            print(
                f"  {pattern[0]}:{pattern[1]:<5} {G:>8}  {q:>6}  {q2:>6}  "
                f"{block_abs:> .12e}  {crude_gh_abs_majorant:> .12e}  {centered_core_majorant:> .12e}  {ratio_crude:> .6f}"
            )
            print(
                f"    core_signed={core: .12e}  ratio_vs_centered={ratio_centered: .6f}  "
                f"nonzero_gh_terms={len(detail)}"
            )
            for abs_term, g, h, term in sorted(detail, reverse=True)[:max(args.coh2_centered_core_top_gh, 0)]:
                print(
                    f"    (g,h)=({g},{h}) term={term: .12e} abs={abs_term: .12e}"
                )
        return

    if args.coh2_signed_structure_report:
        if args.true_series:
            raise SystemExit("--coh2-signed-structure-report is only implemented for the surrogate normalization")

        selected_patterns: set[tuple[int, int]] = set()
        for raw in args.boundary_family_patterns:
            if ":" not in raw:
                raise SystemExit(f"invalid pattern {raw!r}; expected m:n")
            left, right = raw.split(":", 1)
            m = int(left)
            n = int(right)
            if m <= 0 or n <= 0:
                raise SystemExit(f"invalid pattern {raw!r}; entries must be positive")
            selected_patterns.add((m, n) if m <= n else (n, m))

        block_scope = active_support if args.boundary_pattern_g_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in block_scope}

        pair_count_by_block: dict[tuple[tuple[int, int], int], int] = defaultdict(int)
        abs_coeff_proxy_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        total_pairs = len(block_scope) * max(len(block_scope) - 1, 0)
        processed = 0
        started = time.time()
        for q in block_scope:
            cq = coeff_scope[q]
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                processed += 1
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                pair_count_by_block[block] += 1
                abs_coeff_proxy_by_block[block] += abs(cq * coeff_scope[q2])
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[coh2-signed:pass1] processed={processed}/{total_pairs} "
                        f"blocks={len(pair_count_by_block)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        top_remove = max(args.boundary_pattern_g_remove_top, 0)
        candidate_k = (
            max(args.boundary_pattern_g_candidate_blocks, top_remove, args.coh2_signed_structure_top_patterns)
            if args.boundary_pattern_g_candidate_blocks > 0
            else max(max(top_remove, args.coh2_signed_structure_top_patterns) * 10,
                     max(top_remove, args.coh2_signed_structure_top_patterns))
        )
        candidate_blocks = sorted(
            pair_count_by_block.keys(),
            key=lambda block: (
                abs_coeff_proxy_by_block[block],
                pair_count_by_block[block],
                -block[1],
                -block[0][0],
                -block[0][1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_block_set = set(candidate_blocks)

        q_needed: set[int] = set()
        for pattern, G in candidate_blocks:
            m, n = pattern
            q_needed.add(G * m)
            q_needed.add(G * n)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        abs_float_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for q in block_scope:
            for q2 in block_scope:
                if q == q2 or definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                G = math.gcd(q, q2)
                m = q // G
                n = q2 // G
                pattern = (m, n) if m <= n else (n, m)
                block = (pattern, G)
                if block not in candidate_block_set:
                    continue
                processed += 1
                val = surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
                signed_float_by_block[block] += val
                abs_float_by_block[block] += abs(val)
                if args.progress and processed % args.progress_every == 0:
                    elapsed = time.time() - started
                    print(
                        f"[coh2-signed:pass2] processed={processed} "
                        f"candidate_blocks={len(candidate_block_set)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        ranked_blocks = sorted(
            candidate_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                abs(signed_float_by_block[block]),
                abs_coeff_proxy_by_block[block],
            ),
            reverse=True,
        )
        top_global_blocks = set(ranked_blocks[:top_remove])
        expanded_family_blocks = {
            block for block in ranked_blocks[top_remove:]
            if block[0] in selected_patterns
        }
        selected_blocks = top_global_blocks | expanded_family_blocks
        coherent_threshold = 1.0 - 1e-12
        coherent_leftover_blocks = [
            block for block in ranked_blocks
            if block not in selected_blocks
            and pair_count_by_block[block] == 2
            and ((abs(signed_float_by_block[block]) / abs_float_by_block[block]) if abs_float_by_block[block] else 0.0) >= coherent_threshold
        ]
        incoherent_leftover_blocks = [
            block for block in ranked_blocks
            if block not in selected_blocks and block not in coherent_leftover_blocks
        ]

        selected_signed_total = math.fsum(signed_float_by_block[block] for block in selected_blocks)
        selected_abs_signed = abs(selected_signed_total)
        coherent_signed_total = math.fsum(signed_float_by_block[block] for block in coherent_leftover_blocks)
        coherent_abs_total = math.fsum(abs_float_by_block[block] for block in coherent_leftover_blocks)
        incoherent_signed_total = math.fsum(signed_float_by_block[block] for block in incoherent_leftover_blocks)
        incoherent_abs_signed = abs(incoherent_signed_total)
        exact_boundary_signed_total = (
            selected_signed_total + coherent_signed_total + incoherent_signed_total
        )

        signed_group_by_pattern: dict[tuple[tuple[int, int], str], float] = defaultdict(float)
        abs_group_by_pattern: dict[tuple[tuple[int, int], str], float] = defaultdict(float)
        count_group_by_pattern: dict[tuple[tuple[int, int], str], int] = defaultdict(int)
        signed_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        abs_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        positive_blocks: list[tuple[tuple[tuple[int, int], int], float, float]] = []
        negative_blocks: list[tuple[tuple[tuple[int, int], int], float, float]] = []
        for block in coherent_leftover_blocks:
            pattern, _ = block
            signed = signed_float_by_block[block]
            abs_mass = abs_float_by_block[block]
            sign_key = "pos" if signed >= 0 else "neg"
            signed_group_by_pattern[(pattern, sign_key)] += signed
            abs_group_by_pattern[(pattern, sign_key)] += abs_mass
            count_group_by_pattern[(pattern, sign_key)] += 1
            signed_by_pattern[pattern] += signed
            abs_by_pattern[pattern] += abs_mass
            count_by_pattern[pattern] += 1
            record = (block, signed, abs_mass)
            if signed >= 0:
                positive_blocks.append(record)
            else:
                negative_blocks.append(record)

        top_signed_groups = sorted(
            signed_group_by_pattern.keys(),
            key=lambda key: (
                abs_group_by_pattern[key],
                abs(signed_group_by_pattern[key]),
                count_group_by_pattern[key],
                -key[0][0],
                -key[0][1],
                key[1],
            ),
            reverse=True,
        )[:max(args.coh2_signed_structure_top_patterns, 1)]

        top_patterns = sorted(
            abs_by_pattern.keys(),
            key=lambda pat: (
                abs_by_pattern[pat],
                abs(signed_by_pattern[pat]),
                count_by_pattern[pat],
                -pat[0],
                -pat[1],
            ),
            reverse=True,
        )[:max(args.coh2_signed_structure_top_patterns, 1)]

        positive_blocks.sort(key=lambda t: (t[2], abs(t[1])), reverse=True)
        negative_blocks.sort(key=lambda t: (t[2], abs(t[1])), reverse=True)
        top_pos_blocks = positive_blocks[:max(args.coh2_signed_structure_top_blocks, 0)]
        top_neg_blocks = negative_blocks[:max(args.coh2_signed_structure_top_blocks, 0)]

        exact_ranked_blocks = sorted(
            coherent_leftover_blocks,
            key=lambda block: (
                abs_float_by_block[block],
                abs(signed_float_by_block[block]),
                block[1],
                block[0][0],
                block[0][1],
            ),
            reverse=True,
        )
        checkpoints = [100, 500, 1000, 2000, 5000, 10000]
        running_signed = 0.0
        running_abs = 0.0
        topn_rows: list[tuple[int, float, float, float]] = []
        checkpoint_set = {n for n in checkpoints if n <= len(exact_ranked_blocks)}
        for i, block in enumerate(exact_ranked_blocks, start=1):
            signed = signed_float_by_block[block]
            abs_mass = abs_float_by_block[block]
            running_signed += signed
            running_abs += abs_mass
            if i in checkpoint_set:
                tail_abs = coherent_abs_total - running_abs
                cert_bound = abs(selected_signed_total + running_signed) + tail_abs + incoherent_abs_signed
                topn_rows.append((i, running_signed, tail_abs, cert_bound))
        if len(exact_ranked_blocks) not in checkpoint_set:
            tail_abs = coherent_abs_total - running_abs
            cert_bound = abs(selected_signed_total + running_signed) + tail_abs + incoherent_abs_signed
            topn_rows.append((len(exact_ranked_blocks), running_signed, tail_abs, cert_bound))

        print("Surrogate coherent pair-count-2 signed structure report")
        print("  NOTE                      = candidate-scope only; exact_boundary_signed below is not the full surrogate boundary unless candidate blocks exhaust the full scope")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_g_scope}")
        print(f"  candidate blocks evaluated = {len(candidate_blocks)}")
        print(f"  top global blocks selected = {len(top_global_blocks)}")
        print(f"  expanded family patterns   = {sorted(selected_patterns)}")
        print(f"  expanded family blocks     = {len(expanded_family_blocks)}")
        print(f"  coherent pair-count-2 leftover blocks = {len(coherent_leftover_blocks)}")
        print(f"  coherent signed total      = {coherent_signed_total:.12e}")
        print(f"  coherent abs total         = {coherent_abs_total:.12e}")
        print(f"  selected signed total      = {selected_signed_total:.12e}")
        print(f"  incoherent signed total    = {incoherent_signed_total:.12e}")
        print(f"  exact_boundary_signed      = {exact_boundary_signed_total:.12e}")
        print(f"  candidate-scope bound@N=0  = {(selected_abs_signed + coherent_abs_total + incoherent_abs_signed):.12e}")
        print(f"  target_26(full)            = {26.0:.12e}  -- reference only; full-boundary comparison is outside this candidate-scope branch")
        print()
        print("  coherent grouped by (pattern,sign)")
        print("  group         signed               abs                  ratio       block count")
        for pattern, sign_key in top_signed_groups:
            signed = signed_group_by_pattern[(pattern, sign_key)]
            abs_mass = abs_group_by_pattern[(pattern, sign_key)]
            ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
            print(
                f"  {pattern[0]}:{pattern[1]}:{sign_key:<3} {signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}  {count_group_by_pattern[(pattern, sign_key)]:>10}"
            )
        print()
        print("  coherent grouped by pattern")
        print("  pattern       signed               abs                  ratio       block count")
        for pattern in top_patterns:
            signed = signed_by_pattern[pattern]
            abs_mass = abs_by_pattern[pattern]
            ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
            print(
                f"  {pattern[0]}:{pattern[1]:<8} {signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}  {count_by_pattern[pattern]:>10}"
            )
        print()
        print("  top positive coherent blocks")
        print("  pattern   G         q      q'      signed               abs")
        for block, signed, abs_mass in top_pos_blocks:
            pattern, G = block
            m, n = pattern
            print(
                f"  {pattern[0]}:{pattern[1]:<5} {G:>8}  {G*m:>6}  {G*n:>6}  {signed:> .12e}  {abs_mass:> .12e}"
            )
        print()
        print("  top negative coherent blocks")
        print("  pattern   G         q      q'      signed               abs")
        for block, signed, abs_mass in top_neg_blocks:
            pattern, G = block
            m, n = pattern
            print(
                f"  {pattern[0]}:{pattern[1]:<5} {G:>8}  {G*m:>6}  {G*n:>6}  {signed:> .12e}  {abs_mass:> .12e}"
            )
        print()
        print("  candidate-scope certificate bound after exact top-N coherent blocks")
        print("  N       coh2_exact_signed      coh2_tail_abs         bound_value")
        for n, coh2_exact_signed, coh2_tail_abs, bound_value in topn_rows:
            print(
                f"  {n:>5}   {coh2_exact_signed:> .12e}  {coh2_tail_abs:> .12e}  {bound_value:> .12e}"
            )
        return

    if args.emit_boundary_pair_rat is not None:
        if args.true_series:
            raise SystemExit("--emit-boundary-pair-rat is only implemented for the surrogate normalization")
        q, q2 = args.emit_boundary_pair_rat
        if not (1 <= q <= Q0 and 1 <= q2 <= Q0):
            raise SystemExit(f"pair must satisfy 1 <= q,q' <= {Q0}")
        term = surrogate_boundary_pair_contribution_rat(X, q, q2, mu, phi, spf, even_window_card)
        print("Exact surrogate boundary pair contribution certificate")
        print(f"  X                         = {X}")
        print(f"  pair                      = ({q}, {q2})")
        print(f"  rational                  = {term.numerator}/{term.denominator}")
        print(f"  as Lean ℚ                 = {fraction_to_q_literal(term)}")
        print(f"  as decimal                = {float(term):.18f}")
        return

    if args.emit_boundary_rat_total or args.emit_boundary_rat_terms:
        if args.true_series:
            raise SystemExit("--emit-boundary-rat-total/--emit-boundary-rat-terms are only implemented for the surrogate normalization")
        boundary_support = active_support if args.boundary_rat_scope == "active" else support
        support_ordered_pairs = len(boundary_support) * max(len(boundary_support) - 1, 0)
        candidate_pairs: list[tuple[int, int]] = []
        q_needed: set[int] = set()
        scanned = 0
        started_scan = time.time()
        pair_limit = args.pair_limit if args.pair_limit > 0 else 0
        for q in boundary_support:
            for q2 in boundary_support:
                if q == q2:
                    continue
                scanned += 1
                if definitely_zero_surrogate_boundary_pair(q, q2):
                    continue
                candidate_pairs.append((q, q2))
                q_needed.add(q)
                q_needed.add(q2)
                if pair_limit > 0 and len(candidate_pairs) >= pair_limit:
                    break
                if args.progress and scanned % args.progress_every == 0:
                    elapsed = time.time() - started_scan
                    print(
                        f"[boundary-rat:scan] scanned={scanned}/{support_ordered_pairs} "
                        f"candidates={len(candidate_pairs)} q_needed={len(q_needed)} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )
            if pair_limit > 0 and len(candidate_pairs) >= pair_limit:
                break
        if args.progress:
            elapsed = time.time() - started_scan
            print(
                f"[boundary-rat:scan] scanned={scanned}/{support_ordered_pairs} "
                f"candidates={len(candidate_pairs)} q_needed={len(q_needed)} elapsed={elapsed:.1f}s",
                file=sys.stderr,
                flush=True,
            )
        ctx = build_surrogate_boundary_exact_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )
        keep_terms = args.emit_boundary_rat_terms or args.include_terms
        terms: list[tuple[int, int, Fraction]] | None = [] if keep_terms else None
        total = Fraction(0, 1)
        nonzero_count = 0
        processed = 0
        started = time.time()
        total_candidates = len(candidate_pairs)
        for q, q2 in candidate_pairs:
            term = surrogate_boundary_pair_contribution_rat_cached(X, q, q2, ctx)
            processed += 1
            if term != 0:
                total += term
                nonzero_count += 1
                if terms is not None:
                    terms.append((q, q2, term))
            if args.progress and processed % args.progress_every == 0:
                log_exact_progress(processed, total_candidates, nonzero_count, total, started)
        if args.progress:
            log_exact_progress(processed, total_candidates, nonzero_count, total, started)
        print("Exact surrogate boundary rational certificate")
        print(f"  X                         = {X}")
        print(f"  support scope             = {args.boundary_rat_scope}")
        print(f"  support card              = {len(boundary_support)}")
        print(f"  support ordered pairs     = {support_ordered_pairs}")
        print(f"  scanned ordered pairs     = {scanned}")
        print(f"  candidate ordered pairs   = {total_candidates}")
        print(f"  q needed for candidates   = {len(q_needed)}")
        print(f"  processed candidate pairs = {processed}")
        print(f"  nonzero ordered pairs     = {nonzero_count}")
        print(f"  exact total               = {total.numerator}/{total.denominator}")
        print(f"  total as Lean ℚ           = {fraction_to_q_literal(total)}")
        print(f"  total as decimal          = {float(total):.18f}")
        print()
        print(f"nonzero_ordered_pair_count = {nonzero_count}")
        print(f"boundary_rat_total_num = {total.numerator}")
        print(f"boundary_rat_total_den = {total.denominator}")
        print(f"Lean literal: {fraction_to_q_literal(total)}")
        print()
        if args.boundary_rat_scope == "active":
            print("def surrogateBoundaryX0ActiveSignedGenerated : ℚ :=")
            print(f"  {fraction_to_q_literal(total)}")
            print()
            print("-- theorem boundaryActiveCert_true :")
            print("--     surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat X0")
            print("--       = surrogateBoundaryX0ActiveSignedCert := by")
            print("--   -- generated certificate proof")
        else:
            print("def surrogateBoundaryX0RatCertificateSum : ℚ :=")
            print(f"  {fraction_to_q_literal(total)}")
            print()
            print("-- theorem surrogateBoundaryRat_X0_eq_cert :")
            print("--     surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryPairSumUpToQ0Rat X0")
            print("--       = surrogateBoundaryX0FullCert := by")
            print("--   -- generated certificate proof")
        if terms is not None:
            print()
            print("def surrogateBoundaryX0RatCertificateTerms : List ℚ :=")
            print("  [")
            for q, q2, term in terms:
                print(f"    -- (q,q') = ({q},{q2})")
                print(f"    {fraction_to_q_literal(term)},")
            print("  ]")
        return

    if args.emit_diag_tail_direct_term_block_module_for_chunk_index >= 0:
        if args.true_series:
            raise SystemExit("--emit-diag-tail-direct-term-block-module-for-chunk-index is only implemented for the surrogate normalization")
        if args.diag_tail_subchunk_index < 0:
            raise SystemExit("--emit-diag-tail-direct-term-block-module-for-chunk-index requires --diag-tail-subchunk-index")
        chunk_size = max(1, args.diag_tail_chunk_size)
        subchunk_size = max(1, args.diag_tail_subchunk_size)
        block_size = max(1, args.diag_tail_block_size)
        block_start_index = max(0, args.diag_tail_block_start_index)
        block_count = max(1, args.diag_tail_block_count)
        tail_support = [
            q for q in support
            if q not in DIAG_MAIN_LOW_Q and q > 50
        ]
        chunk_count = math.ceil(len(tail_support) / chunk_size)
        chunk_index = args.emit_diag_tail_direct_term_block_module_for_chunk_index
        if chunk_index >= chunk_count:
            raise SystemExit(
                f"--emit-diag-tail-direct-term-block-module-for-chunk-index={chunk_index} out of range for "
                f"{chunk_count} chunks with size {chunk_size}"
            )
        start_idx = chunk_index * chunk_size
        chunk_support = tail_support[start_idx:start_idx + chunk_size]
        subchunk_index = args.diag_tail_subchunk_index
        explicit_sub_start = args.diag_tail_subchunk_start_offset
        subchunk_count = math.ceil(len(chunk_support) / subchunk_size)
        if explicit_sub_start >= 0:
            sub_start = explicit_sub_start
            if sub_start >= len(chunk_support):
                raise SystemExit(
                    f"--diag-tail-subchunk-start-offset={sub_start} out of range for "
                    f"chunk {chunk_index} with size {len(chunk_support)}"
                )
        else:
            if subchunk_index >= subchunk_count:
                raise SystemExit(
                    f"--diag-tail-subchunk-index={subchunk_index} out of range for "
                    f"{subchunk_count} subchunks in chunk {chunk_index}"
                )
            sub_start = subchunk_index * subchunk_size
        sub_support = chunk_support[sub_start:sub_start + subchunk_size]
        block_total_count = math.ceil(len(sub_support) / block_size)
        if block_start_index >= block_total_count:
            raise SystemExit(
                f"--diag-tail-block-start-index={block_start_index} out of range for "
                f"{block_total_count} blocks of size {block_size}"
            )
        block_end_index = min(block_total_count, block_start_index + block_count)
        if block_start_index >= block_end_index:
            raise SystemExit("empty block range requested")

        chunk_label = f"{chunk_index:03d}"
        sub_label = f"{subchunk_index:03d}"
        requested_block_support: list[int] = []
        for block_index in range(block_start_index, block_end_index):
            block_rel_start = block_index * block_size
            requested_block_support.extend(
                sub_support[block_rel_start:block_rel_start + block_size]
            )
        diag_ctx = build_surrogate_diagonal_exact_context(
            mu, phi, spf, requested_block_support
        )

        def qlit(frac: Fraction) -> str:
            return fraction_to_q_literal(frac)

        def emit_sum_def(name: str, support_names: list[str]) -> None:
            if not support_names:
                print(f"def {name} (X0 : ℕ) : ℚ := (0 : ℚ)")
                return
            print(f"def {name} (X0 : ℕ) : ℚ :=")
            for i, support_name in enumerate(support_names):
                prefix = "  " if i == 0 else "    + "
                print(f"{prefix}(∑ q ∈ {support_name},")
                print("        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")

        def emit_const_def(name: str, part_names: list[str]) -> None:
            if not part_names:
                print(f"def {name} : ℚ := (0 : ℚ)")
                return
            print(f"def {name} : ℚ :=")
            for i, part_name in enumerate(part_names):
                prefix = "  " if i == 0 else "    + "
                print(f"{prefix}{part_name}")

        print("import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25")
        print()
        print("namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")
        print()
        print("open scoped BigOperators")
        print()
        print("open Goldbach")
        print("open Goldbach.BankParams")
        print("open Goldbach.Windows")
        print()
        print(
            f"/- Generated direct-term certificate blocks for tail chunk {chunk_label}, "
            f"subchunk {sub_label}, blocks [{block_start_index},{block_end_index}). -/"
        )
        print()

        for block_index in range(block_start_index, block_end_index):
            block_rel_start = block_index * block_size
            block_support = sub_support[block_rel_start:block_rel_start + block_size]
            block_abs_start = start_idx + sub_start + block_rel_start
            block_abs_end = block_abs_start + len(block_support)
            block_name = f"surrogateDiagTailX0RatChunk{chunk_label}Sub{sub_label}Block{block_index:03d}"
            block_sum_name = f"surrogateDiagonalTailChunk{chunk_label}Sub{sub_label}Block{block_index:03d}Sum"
            block_label = f"TailChunk{chunk_label}Sub{sub_label}Block{block_index:03d}"
            print(
                f"/-- Block {block_index:03d} covers tail-support indices "
                f"[{block_abs_start},{block_abs_end}) and q from {block_support[0]} to {block_support[-1]}. -/"
            )
            print()

            part_names: list[str] = []
            support_names: list[str] = []

            for part_index, q in enumerate(block_support):
                term_total = surrogate_diagonal_energy_q_rat_cached(
                    X, q, even_window_card, diag_ctx
                )
                part_name = f"{block_name}Part{part_index:03d}"
                support_name = f"{block_label}Part{part_index:03d}SupportExplicit"
                cert_name = f"SurrogateDiagonal{block_label}Part{part_index:03d}CertificateAtX0"
                theorem_name = f"surrogateDiagonal{block_label}Part{part_index:03d}_eq_cert_explicit"
                part_names.append(part_name)
                support_names.append(support_name)
                print(f"def {support_name} : Finset ℕ :=")
                print(f"  {nat_list_to_lean_finset_literal([q])}")
                print()
                print(f"def {part_name} : ℚ :=")
                print(f"  {qlit(term_total)}")
                print()
                print(f"def {cert_name} : Prop :=")
                print(f"  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 {q}")
                print(f"    = {part_name}")
                print()
                print(f"theorem {theorem_name} :")
                print(f"    {cert_name} →")
                print(f"    (∑ q ∈ {support_name},")
                print("        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
                print(f"      = {part_name} := by")
                print("  intro hcert")
                print(f"  unfold {cert_name} at hcert")
                print(f"  simpa [{support_name}, {part_name}] using hcert")
                print()

            head_parts = list(range(0, min(10, len(part_names))))
            mid_parts = list(range(min(10, len(part_names)), min(20, len(part_names))))
            tail_parts = list(range(min(20, len(part_names)), len(part_names)))

            head_sum_name = f"surrogateDiagonal{block_label}HeadSum"
            mid_sum_name = f"surrogateDiagonal{block_label}MidSum"
            tail_sum_name = f"surrogateDiagonal{block_label}TailSum"
            head_const_name = f"{block_name}Head"
            mid_const_name = f"{block_name}Mid"
            tail_const_name = f"{block_name}Tail"
            head_cert_name = f"SurrogateDiagonal{block_label}HeadCertificateAt"
            mid_cert_name = f"SurrogateDiagonal{block_label}MidCertificateAt"
            tail_cert_name = f"SurrogateDiagonal{block_label}TailCertificateAt"
            arith_name = f"{block_name}_eq_head_add_mid_add_tail"
            block_theorem_name = f"surrogateDiagonal{block_label}_eq_cert_explicit"

            emit_sum_def(head_sum_name, [support_names[i] for i in head_parts])
            print()
            emit_const_def(head_const_name, [part_names[i] for i in head_parts])
            print()
            emit_sum_def(mid_sum_name, [support_names[i] for i in mid_parts])
            print()
            emit_const_def(mid_const_name, [part_names[i] for i in mid_parts])
            print()
            emit_sum_def(tail_sum_name, [support_names[i] for i in tail_parts])
            print()
            emit_const_def(tail_const_name, [part_names[i] for i in tail_parts])
            print()
            print(f"def {block_sum_name} (X0 : ℕ) : ℚ :=")
            print(f"  {head_sum_name} X0")
            print(f"    + {mid_sum_name} X0")
            print(f"    + {tail_sum_name} X0")
            print()
            emit_const_def(block_name, part_names)
            print()
            print(f"theorem {arith_name} :")
            print(f"    {head_const_name} + {mid_const_name} + {tail_const_name} =")
            print(f"      {block_name} := by")
            print(f"  unfold {head_const_name} {mid_const_name} {tail_const_name} {block_name}")
            print("  ring")
            print()
            print(f"def {head_cert_name} (X0 : ℕ) : Prop :=")
            print(f"  {head_sum_name} X0 = {head_const_name}")
            print()
            print(f"def {mid_cert_name} (X0 : ℕ) : Prop :=")
            print(f"  {mid_sum_name} X0 = {mid_const_name}")
            print()
            print(f"def {tail_cert_name} (X0 : ℕ) : Prop :=")
            print(f"  {tail_sum_name} X0 = {tail_const_name}")
            print()
            print(f"theorem {block_theorem_name}")
            print(f"    (hHead : {head_cert_name} X0)")
            print(f"    (hMid : {mid_cert_name} X0)")
            print(f"    (hTail : {tail_cert_name} X0) :")
            print(f"    {block_sum_name} X0 = {block_name} := by")
            print(f"  unfold {head_cert_name} at hHead")
            print(f"  unfold {mid_cert_name} at hMid")
            print(f"  unfold {tail_cert_name} at hTail")
            print(f"  unfold {block_sum_name}")
            print("  rw [hHead, hMid, hTail]")
            print(f"  exact {arith_name}")
            print()

        print("end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")
        return

    coeff_q: dict[int, float] = {}
    diag_energy_q: dict[int, float] = {}
    diagonal = 0.0
    total_vec = [0.0] * even_window_card

    # Exact diagonal and total truncation observable on the full coefficient support.
    for q in support:
        c_q = normalized_sigma_trunc_summand_real_coeff(q, mu, phi)
        coeff_q[q] = c_q
        vals = [c_q * float(ramanujan_sum(q, N, mu, phi)) for N in even_window]
        avg = math.fsum(vals) / float(even_window_card)
        centered_vals = [v - avg for v in vals]
        eq = math.fsum(v * v for v in centered_vals)
        diag_energy_q[q] = eq
        diagonal += eq
        for i, v in enumerate(centered_vals):
            total_vec[i] += v

    total_window_energy = math.fsum(v * v for v in total_vec)
    pair_correlation_total = total_window_energy - diagonal

    diag_main = math.fsum(eq for q, eq in diag_energy_q.items() if q in DIAG_MAIN_LOW_Q)
    diag_small_rest = math.fsum(
        eq for q, eq in diag_energy_q.items() if q not in DIAG_MAIN_LOW_Q and q <= 50
    )
    diag_tail = math.fsum(
        eq for q, eq in diag_energy_q.items() if q not in DIAG_MAIN_LOW_Q and q > 50
    )
    diag_small_rest_support = sorted(
        q for q, eq in diag_energy_q.items()
        if q not in DIAG_MAIN_LOW_Q and q <= 50 and eq != 0.0
    )

    def rescale(value: float) -> float:
        return value * scale_sq

    def coeff_for_print(q: int) -> float:
        if not args.true_series:
            return coeff_q[q]
        return coeff_q[q] * scale_factor

    def print_normalization_header() -> None:
        print(f"X = {X}")
        if args.true_series:
            print("normalization            = true-series numerical mode")
            print(f"  C2_surrogate           = {C2_NUMERIC:.15f}")
            print(f"  C2_true_approx         = {true_c2:.15f}")
            print(f"  C2_true_abs_error_up   = {true_c2_abs_error:.3e}")
            print(f"  sigma(2)_true_approx   = {2.0 * true_c2:.15f}")
            print(f"  coeff scale            = C2_surrogate / C2_true ≈ {scale_factor:.15f}")
            print(f"  energy scale           = coeff scale^2 ≈ {scale_sq:.15f}")
            print(f"  energy scale abs err   = {scale_sq_abs_error:.3e}")
            print("  NOTE                   = all downstream direct quantities scale exactly by energy scale once C2 is fixed")
        else:
            print("normalization            = surrogate mode")
            print(f"  C2_surrogate           = {C2_NUMERIC:.15f}")
        print(f"even window card = {even_window_card}")
        print(f"coeff support card = {len(support)}")

    if args.diag_only and args.emit_diag_single_q_rat_data < 0:
        print_normalization_header()
        print()
        print(f"diagonalExact              = {rescale(diagonal):.12f}")
        print(f"windowEnergyExact          = {rescale(total_window_energy):.12f}")
        print(f"pairCorrelationTotal       = {rescale(pair_correlation_total):.12f}")
        if total_window_energy != 0.0:
            print(f"diagonalShareOfEnergy      = {diagonal / total_window_energy:.12f}")
            print(f"offdiagShareOfEnergy       = {pair_correlation_total / total_window_energy:.12f}")

        if args.diag_breakdown:
            print()
            print("Diagonal per-q breakdown")
            print(f"  total diagonal = {rescale(diagonal):.12f}")
            print(f"  support size = {len(support)}")
            print(f"  off-support q count = {Q0 - len(support)} (exactly zero by coefficient support)")
            print()
            print("Diagonal main/small-rest/tail split")
            print("  piece        mass                 share")
            for label, mass in [
                ("main", diag_main),
                ("smallRest", diag_small_rest),
                ("tail", diag_tail),
            ]:
                share = (mass / diagonal) if diagonal else 0.0
                print(f"  {label:<10} {rescale(mass):> .12e}  {share:> .6f}")

            top = min(args.diag_top, len(support))
            top_qs = sorted(diag_energy_q.items(), key=lambda kv: kv[1], reverse=True)[:top]
            print()
            print(f"Top {top} q by diagonal energy")
            print("  q      support  coeff               E_q                 share        cumulative")
            cumulative = 0.0
            for q, eq in top_qs:
                cumulative += eq
                share = (eq / diagonal) if diagonal else 0.0
                cshare = (cumulative / diagonal) if diagonal else 0.0
                print(
                    f"  {q:>5}  yes      {coeff_for_print(q):> .12e}  {rescale(eq):> .12e}  {share:> .6f}    {cshare:> .6f}"
                )

            print()
            print("Mass by increasing q range")
            ranges = [
                (1, 10),
                (11, 50),
                (51, 100),
                (101, 500),
                (501, 1000),
                (1001, 5000),
                (5001, Q0),
            ]
            print("  range           signed/abs mass      share")
            for lo, hi in ranges:
                mass = math.fsum(eq for q, eq in diag_energy_q.items() if lo <= q <= hi)
                share = (mass / diagonal) if diagonal else 0.0
                print(f"  [{lo:>4},{hi:>5}]   {rescale(mass):> .12e}  {share:> .6f}")

            omega_mass: dict[int, float] = defaultdict(float)
            spf_mass: dict[int, float] = defaultdict(float)
            increasing_cumulative = 0.0
            print()
            print("First support q by increasing q")
            print("  q      coeff               E_q                 cumulative")
            for q in sorted(support)[:top]:
                increasing_cumulative += diag_energy_q[q]
                cshare = (increasing_cumulative / diagonal) if diagonal else 0.0
                print(
                    f"  {q:>5}  {coeff_for_print(q):> .12e}  {rescale(diag_energy_q[q]):> .12e}  {cshare:> .6f}"
                )

            for q, eq in diag_energy_q.items():
                fac = factorization(q, spf)
                omega_mass[len(fac)] += eq
                if fac:
                    spf_mass[min(fac)] += eq
                else:
                    spf_mass[1] += eq

            print()
            print("Mass by omega(q)")
            print("  omega   mass                 share")
            for omega in sorted(omega_mass):
                mass = omega_mass[omega]
                share = (mass / diagonal) if diagonal else 0.0
                print(f"  {omega:>5}   {rescale(mass):> .12e}  {share:> .6f}")

            print()
            print("Mass by smallest prime factor")
            print("  spf     mass                 share")
            for p, mass in sorted(spf_mass.items(), key=lambda kv: (-kv[1], kv[0])):
                share = (mass / diagonal) if diagonal else 0.0
                print(f"  {p:>5}   {rescale(mass):> .12e}  {share:> .6f}")
        return

    if args.emit_diag_tail_rat_total:
        if args.true_series:
            raise SystemExit("--emit-diag-tail-rat-total is only implemented for the surrogate normalization")
        tail_support = [
            q for q in support
            if q not in DIAG_MAIN_LOW_Q and q > 50
        ]
        total_rat = Fraction(0, 1)
        started = time.time()
        for i, q in enumerate(tail_support, start=1):
            total_rat += surrogate_diagonal_energy_q_rat(X, q, mu, phi, even_window, even_window_card)
            if args.progress and (i % max(1, args.progress_every) == 0 or i == len(tail_support)):
                elapsed = time.time() - started
                print(
                    f"[diag-tail-rat] q={i}/{len(tail_support)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )
        print("Surrogate diagonal tail exact rational total")
        print(f"  X                         = {X}")
        print(f"  tail support card         = {len(tail_support)}")
        print(f"  rational total numerator  = {total_rat.numerator}")
        print(f"  rational total denominator= {total_rat.denominator}")
        print(f"  Lean ℚ literal            = {fraction_to_q_literal(total_rat)}")
        print(f"  float value               = {float(total_rat):.15f}")
        print("  Lean payload")
        print(f"def surrogateDiagTailX0RatCert : ℚ := {fraction_to_q_literal(total_rat)}")
        print()
        print("theorem surrogateDiagTailX0RatCert_le_check :")
        print("    surrogateDiagTailX0RatCert ≤ surrogateDiagTailX0Check.lhs := by")
        print("  norm_num [surrogateDiagTailX0RatCert, surrogateDiagTailX0Check]")
        return

    if args.emit_diag_single_q_rat_data >= 0:
        q = args.emit_diag_single_q_rat_data
        if q < 1 or q > Q0:
            raise SystemExit(f"--emit-diag-single-q-rat-data={q} is out of range 1..{Q0}")
        diag_ctx = build_surrogate_diagonal_exact_context(mu, phi, spf, [q])
        fac_q = factorization(q, spf)
        divs_q = divisors_from_factorization(fac_q)
        coeff_q = surrogate_coeff_rat(q, mu, phi)
        energy_q = centered_ramanujan_window_energy_rat_cached(X, q, even_window_card, diag_ctx)
        term_q = surrogate_diagonal_energy_q_rat_cached(X, q, even_window_card, diag_ctx)
        print("Surrogate diagonal single-q exact rational data")
        print(f"  X                         = {X}")
        print(f"  q                         = {q}")
        print(f"  squarefree                = {mu[q] != 0}")
        print(f"  totient                   = {phi[q]}")
        print(f"  divisors                  = {divs_q}")
        print(f"  coeff rat                 = {fraction_to_q_literal(coeff_q)}")
        print(f"  energy rat                = {fraction_to_q_literal(energy_q)}")
        print(f"  term rat                  = {fraction_to_q_literal(term_q)}")
        print("  gcd-class table")
        for g in divs_q:
            count_g = Fraction(
                gcd_class_count_in_even_progression(
                    q, g, even_window_progression(X)[0], even_window_progression(X)[1], diag_ctx
                ),
                1,
            )
            avg_g = count_g / even_window_card
            coeff_g = ramanujan_gcd_class_coeff_rat(q, g, mu, phi)
            print(
                "    "
                f"g={g:<6} coeff={fraction_to_q_literal(coeff_g):>12} "
                f"count={count_g.numerator:<8} avg={fraction_to_q_literal(avg_g)}"
            )
        print("  Lean payload")
        print(f"-- q = {q}")
        print(f"-- divisors: {divs_q}")
        print(f"-- coeff: {fraction_to_q_literal(coeff_q)}")
        print(f"-- energy: {fraction_to_q_literal(energy_q)}")
        print(f"-- term: {fraction_to_q_literal(term_q)}")
        return

    if args.emit_diag_tail_rat_chunks:
        if args.true_series:
            raise SystemExit("--emit-diag-tail-rat-chunks is only implemented for the surrogate normalization")
        chunk_size = max(1, args.diag_tail_chunk_size)
        tail_support = [
            q for q in support
            if q not in DIAG_MAIN_LOW_Q and q > 50
        ]
        chunk_payloads = []
        total_rat = Fraction(0, 1)
        started = time.time()
        for chunk_index, start_idx in enumerate(range(0, len(tail_support), chunk_size)):
            chunk_support = tail_support[start_idx:start_idx + chunk_size]
            chunk_total = Fraction(0, 1)
            for q in chunk_support:
                chunk_total += surrogate_diagonal_energy_q_rat(
                    X, q, mu, phi, even_window, even_window_card
                )
            total_rat += chunk_total
            chunk_payloads.append((chunk_index, start_idx, start_idx + len(chunk_support), chunk_support[0], chunk_support[-1], chunk_total))
            if args.progress:
                elapsed = time.time() - started
                print(
                    f"[diag-tail-rat-chunks] chunk={chunk_index + 1}/{math.ceil(len(tail_support) / chunk_size)} "
                    f"q={start_idx + len(chunk_support)}/{len(tail_support)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )
        print("Surrogate diagonal tail exact rational chunks")
        print(f"  X                         = {X}")
        print(f"  tail support card         = {len(tail_support)}")
        print(f"  chunk size                = {chunk_size}")
        print(f"  chunk count               = {len(chunk_payloads)}")
        print(f"  rational total numerator  = {total_rat.numerator}")
        print(f"  rational total denominator= {total_rat.denominator}")
        print(f"  Lean ℚ literal            = {fraction_to_q_literal(total_rat)}")
        print(f"  float value               = {float(total_rat):.15f}")
        print("  Chunk table")
        for chunk_index, start_idx, end_idx, first_q, last_q, chunk_total in chunk_payloads:
            print(
                f"    chunk {chunk_index:03d}: idx=[{start_idx},{end_idx}) "
                f"q=[{first_q},{last_q}] value={fraction_to_q_literal(chunk_total)}"
            )
        print("  Lean payload")
        for chunk_index, start_idx, end_idx, first_q, last_q, chunk_total in chunk_payloads:
            print(
                f"def surrogateDiagTailX0RatChunk{chunk_index:03d} : ℚ := "
                f"{fraction_to_q_literal(chunk_total)}"
            )
            print(
                f"-- chunk {chunk_index:03d} covers tail-support indices [{start_idx},{end_idx}) "
                f"and q from {first_q} to {last_q}"
            )
        chunk_names = [f"surrogateDiagTailX0RatChunk{chunk_index:03d}" for chunk_index, *_ in chunk_payloads]
        chunk_sum_expr = " + ".join(chunk_names) if chunk_names else "(0 : ℚ)"
        print()
        print("theorem surrogateDiagTailX0RatCert_eq_chunk_sum :")
        print(f"    {chunk_sum_expr} = surrogateDiagTailX0RatCert := by")
        print("  norm_num [surrogateDiagTailX0RatCert,")
        for i, name in enumerate(chunk_names):
            comma = "," if i + 1 < len(chunk_names) else ""
            print(f"    {name}{comma}")
        print("  ]")
        print()
        print("theorem surrogateDiagonalTailRat_X0_eq_cert_of_chunked_sum")
        print("    (hchunked :")
        print("      surrogateCenteredNormalizedSigmaTruncDiagonalEnergyDirectTailRat X0")
        print(f"        = {chunk_sum_expr}) :")
        print("    surrogateCenteredNormalizedSigmaTruncDiagonalEnergyDirectTailRat X0")
        print("      = surrogateDiagTailX0RatCert := by")
        print("  rw [hchunked, surrogateDiagTailX0RatCert_eq_chunk_sum]")
        return

    if args.emit_diag_tail_rat_chunk_index >= 0:
        if args.true_series:
            raise SystemExit("--emit-diag-tail-rat-chunk-index is only implemented for the surrogate normalization")
        chunk_size = max(1, args.diag_tail_chunk_size)
        tail_support = [
            q for q in support
            if q not in DIAG_MAIN_LOW_Q and q > 50
        ]
        chunk_count = math.ceil(len(tail_support) / chunk_size)
        chunk_index = args.emit_diag_tail_rat_chunk_index
        if chunk_index >= chunk_count:
            raise SystemExit(
                f"--emit-diag-tail-rat-chunk-index={chunk_index} out of range for "
                f"{chunk_count} chunks with size {chunk_size}"
            )
        start_idx = chunk_index * chunk_size
        chunk_support = tail_support[start_idx:start_idx + chunk_size]
        chunk_total = Fraction(0, 1)
        started = time.time()
        for i, q in enumerate(chunk_support, start=1):
            chunk_total += surrogate_diagonal_energy_q_rat(
                X, q, mu, phi, even_window, even_window_card
            )
            if args.progress and (i % max(1, args.progress_every) == 0 or i == len(chunk_support)):
                elapsed = time.time() - started
                print(
                    f"[diag-tail-rat-chunk] chunk={chunk_index}/{chunk_count} "
                    f"q={i}/{len(chunk_support)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )
        end_idx = start_idx + len(chunk_support)
        print("Surrogate diagonal tail exact rational chunk")
        print(f"  X                         = {X}")
        print(f"  tail support card         = {len(tail_support)}")
        print(f"  chunk size                = {chunk_size}")
        print(f"  chunk index               = {chunk_index}")
        print(f"  chunk count               = {chunk_count}")
        print(f"  chunk support indices     = [{start_idx}, {end_idx})")
        print(f"  chunk q range             = [{chunk_support[0]}, {chunk_support[-1]}]")
        print(f"  rational numerator        = {chunk_total.numerator}")
        print(f"  rational denominator      = {chunk_total.denominator}")
        print(f"  Lean ℚ literal            = {fraction_to_q_literal(chunk_total)}")
        print(f"  float value               = {float(chunk_total):.15f}")
        print("  Lean payload")
        print(
            f"def surrogateDiagTailX0RatChunk{chunk_index:03d} : ℚ := "
            f"{fraction_to_q_literal(chunk_total)}"
        )
        print(
            f"-- chunk {chunk_index:03d} covers tail-support indices [{start_idx},{end_idx}) "
            f"and q from {chunk_support[0]} to {chunk_support[-1]}"
        )
        return

    if args.emit_diag_tail_rat_one_subchunk_for_chunk_index >= 0:
        if args.true_series:
            raise SystemExit("--emit-diag-tail-rat-one-subchunk-for-chunk-index is only implemented for the surrogate normalization")
        if args.diag_tail_subchunk_index < 0:
            raise SystemExit("--emit-diag-tail-rat-one-subchunk-for-chunk-index requires --diag-tail-subchunk-index")
        chunk_size = max(1, args.diag_tail_chunk_size)
        subchunk_size = max(1, args.diag_tail_subchunk_size)
        tail_support = [
            q for q in support
            if q not in DIAG_MAIN_LOW_Q and q > 50
        ]
        chunk_count = math.ceil(len(tail_support) / chunk_size)
        chunk_index = args.emit_diag_tail_rat_one_subchunk_for_chunk_index
        if chunk_index >= chunk_count:
            raise SystemExit(
                f"--emit-diag-tail-rat-one-subchunk-for-chunk-index={chunk_index} out of range for "
                f"{chunk_count} chunks with size {chunk_size}"
            )
        start_idx = chunk_index * chunk_size
        chunk_support = tail_support[start_idx:start_idx + chunk_size]
        subchunk_index = args.diag_tail_subchunk_index
        explicit_sub_start = args.diag_tail_subchunk_start_offset
        subchunk_count = math.ceil(len(chunk_support) / subchunk_size)
        if explicit_sub_start >= 0:
            sub_start = explicit_sub_start
            if sub_start >= len(chunk_support):
                raise SystemExit(
                    f"--diag-tail-subchunk-start-offset={sub_start} out of range for "
                    f"chunk {chunk_index} with size {len(chunk_support)}"
                )
        else:
            if subchunk_index >= subchunk_count:
                raise SystemExit(
                    f"--diag-tail-subchunk-index={subchunk_index} out of range for "
                    f"{subchunk_count} subchunks in chunk {chunk_index}"
                )
            sub_start = subchunk_index * subchunk_size
        sub_support = chunk_support[sub_start:sub_start + subchunk_size]
        sub_total = Fraction(0, 1)
        started = time.time()
        for i, q in enumerate(sub_support, start=1):
            sub_total += surrogate_diagonal_energy_q_rat(
                X, q, mu, phi, even_window, even_window_card
            )
            if args.progress and (i % max(1, args.progress_every) == 0 or i == len(sub_support)):
                elapsed = time.time() - started
                print(
                    f"[diag-tail-rat-one-subchunk] chunk={chunk_index}/{chunk_count} "
                    f"subchunk={subchunk_index + 1}/{subchunk_count} q={i}/{len(sub_support)} "
                    f"elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )
        chunk_label = f"{chunk_index:03d}"
        sub_name = f"surrogateDiagTailX0RatChunk{chunk_label}Sub{subchunk_index:03d}"
        sub_support_name = (
            f"centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk{chunk_label}"
            f"Sub{subchunk_index:03d}SupportAtX0"
        )
        theorem_stub_name = f"surrogateDiagonalTailChunk{chunk_label}Sub{subchunk_index:03d}_eq_cert"
        abs_start = start_idx + sub_start
        abs_end = abs_start + len(sub_support)
        print("Surrogate diagonal tail exact rational single subchunk")
        print(f"  X                         = {X}")
        print(f"  tail support card         = {len(tail_support)}")
        print(f"  chunk size                = {chunk_size}")
        print(f"  subchunk size             = {subchunk_size}")
        print(f"  chunk index               = {chunk_index}")
        print(f"  subchunk index            = {subchunk_index}")
        print(f"  support indices           = [{abs_start}, {abs_end})")
        print(f"  q range                   = [{sub_support[0]}, {sub_support[-1]}]")
        print(f"  rational numerator        = {sub_total.numerator}")
        print(f"  rational denominator      = {sub_total.denominator}")
        print(f"  Lean ℚ literal            = {fraction_to_q_literal(sub_total)}")
        print(f"  float value               = {float(sub_total):.15f}")
        print("  Lean payload")
        print(f"def {sub_name} : ℚ := {fraction_to_q_literal(sub_total)}")
        print(f"-- support def: {sub_support_name}")
        part_size = max(0, args.diag_tail_one_subchunk_part_size)
        if part_size > 0:
            print(f"  part size                 = {part_size}")
            part_names = []
            part_support_names = []
            print("  Part table")
            for part_index, part_start in enumerate(range(0, len(sub_support), part_size)):
                part_support = sub_support[part_start:part_start + part_size]
                part_total = Fraction(0, 1)
                for q in part_support:
                    part_total += surrogate_diagonal_energy_q_rat(
                        X, q, mu, phi, even_window, even_window_card
                    )
                part_name = f"{sub_name}Part{part_index:03d}"
                part_support_name = f"{sub_support_name}Part{part_index:03d}Explicit"
                part_names.append(part_name)
                part_support_names.append(part_support_name)
                part_abs_start = abs_start + part_start
                part_abs_end = part_abs_start + len(part_support)
                print(
                    f"    part {part_index:03d}: idx=[{part_abs_start},{part_abs_end}) "
                    f"q=[{part_support[0]},{part_support[-1]}] "
                    f"value={fraction_to_q_literal(part_total)}"
                )
                print(f"def {part_name} : ℚ := {fraction_to_q_literal(part_total)}")
                print(
                    f"def {part_support_name} : Finset ℕ := "
                    f"{nat_list_to_lean_finset_literal(part_support)}"
                )
                print(f"theorem {theorem_stub_name}Part{part_index:03d} :")
                print(f"    (∑ q ∈ {part_support_name},")
                print("        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
                print(f"      = {part_name} := by")
                print(
                    f"  -- part {part_index:03d} of subchunk {subchunk_index:03d} "
                    f"covers tail-support indices [{part_abs_start},{part_abs_end}) "
                    f"and q from {part_support[0]} to {part_support[-1]}"
                )
                print("  -- generated certificate proof")
                print()
            print(
                f"def {sub_support_name}Explicit : Finset ℕ := "
                f"{nat_list_to_lean_finset_literal(sub_support)}"
            )
            part_sum_expr = " + ".join(part_names) if part_names else "(0 : ℚ)"
            print(f"theorem {sub_name}_eq_part_sum :")
            print(f"    {part_sum_expr} = {sub_name} := by")
            print(f"  norm_num [{sub_name},")
            for i, name in enumerate(part_names):
                comma = "," if i + 1 < len(part_names) else ""
                print(f"    {name}{comma}")
            print("  ]")
            print(f"theorem {theorem_stub_name} :")
            print(f"    (∑ q ∈ {sub_support_name}Explicit,")
            print("        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
            print(f"      = {sub_name} := by")
            print(
                f"  -- combine the part certificates for subchunk {subchunk_index:03d}"
            )
            print("  -- generated certificate proof")
        else:
            print(
                f"def {sub_support_name}Explicit : Finset ℕ := "
                f"{nat_list_to_lean_finset_literal(sub_support)}"
            )
            print(f"theorem {theorem_stub_name} :")
            print(f"    (∑ q ∈ {sub_support_name}Explicit,")
            print("        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
            print(f"      = {sub_name} := by")
            print(
                f"  -- subchunk {subchunk_index:03d} covers tail-support indices [{abs_start},{abs_end}) "
                f"and q from {sub_support[0]} to {sub_support[-1]}"
            )
            print("  -- generated certificate proof")
        return

    if args.emit_diag_tail_direct_term_block_module_for_chunk_index >= 0:
        if args.true_series:
            raise SystemExit("--emit-diag-tail-direct-term-block-module-for-chunk-index is only implemented for the surrogate normalization")
        if args.diag_tail_subchunk_index < 0:
            raise SystemExit("--emit-diag-tail-direct-term-block-module-for-chunk-index requires --diag-tail-subchunk-index")
        chunk_size = max(1, args.diag_tail_chunk_size)
        subchunk_size = max(1, args.diag_tail_subchunk_size)
        block_size = max(1, args.diag_tail_block_size)
        block_start_index = max(0, args.diag_tail_block_start_index)
        block_count = max(1, args.diag_tail_block_count)
        tail_support = [
            q for q in support
            if q not in DIAG_MAIN_LOW_Q and q > 50
        ]
        chunk_count = math.ceil(len(tail_support) / chunk_size)
        chunk_index = args.emit_diag_tail_direct_term_block_module_for_chunk_index
        if chunk_index >= chunk_count:
            raise SystemExit(
                f"--emit-diag-tail-direct-term-block-module-for-chunk-index={chunk_index} out of range for "
                f"{chunk_count} chunks with size {chunk_size}"
            )
        start_idx = chunk_index * chunk_size
        chunk_support = tail_support[start_idx:start_idx + chunk_size]
        subchunk_index = args.diag_tail_subchunk_index
        explicit_sub_start = args.diag_tail_subchunk_start_offset
        subchunk_count = math.ceil(len(chunk_support) / subchunk_size)
        if explicit_sub_start >= 0:
            sub_start = explicit_sub_start
            if sub_start >= len(chunk_support):
                raise SystemExit(
                    f"--diag-tail-subchunk-start-offset={sub_start} out of range for "
                    f"chunk {chunk_index} with size {len(chunk_support)}"
                )
        else:
            if subchunk_index >= subchunk_count:
                raise SystemExit(
                    f"--diag-tail-subchunk-index={subchunk_index} out of range for "
                    f"{subchunk_count} subchunks in chunk {chunk_index}"
                )
            sub_start = subchunk_index * subchunk_size
        sub_support = chunk_support[sub_start:sub_start + subchunk_size]
        block_total_count = math.ceil(len(sub_support) / block_size)
        if block_start_index >= block_total_count:
            raise SystemExit(
                f"--diag-tail-block-start-index={block_start_index} out of range for "
                f"{block_total_count} blocks of size {block_size}"
            )
        block_end_index = min(block_total_count, block_start_index + block_count)
        if block_start_index >= block_end_index:
            raise SystemExit("empty block range requested")

        chunk_label = f"{chunk_index:03d}"
        sub_label = f"{subchunk_index:03d}"
        module_basename = (
            args.diag_tail_module_name.strip()
            or f"Q0MinorZeroModeNormalizedAverageX0TailChunk{chunk_label}Sub{sub_label}"
        )
        requested_block_support: list[int] = []
        for block_index in range(block_start_index, block_end_index):
            block_rel_start = block_index * block_size
            requested_block_support.extend(
                sub_support[block_rel_start:block_rel_start + block_size]
            )
        diag_ctx = build_surrogate_diagonal_exact_context(
            mu, phi, spf, requested_block_support
        )

        def qlit(frac: Fraction) -> str:
            return fraction_to_q_literal(frac)

        def emit_sum_def(name: str, support_names: list[str]) -> None:
            if not support_names:
                print(f"def {name} (X0 : ℕ) : ℚ := (0 : ℚ)")
                return
            print(f"def {name} (X0 : ℕ) : ℚ :=")
            for i, support_name in enumerate(support_names):
                prefix = "  " if i == 0 else "    + "
                print(
                    f"{prefix}(∑ q ∈ {support_name},"
                )
                print(
                    "        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)"
                )

        def emit_const_def(name: str, part_names: list[str]) -> None:
            if not part_names:
                print(f"def {name} : ℚ := (0 : ℚ)")
                return
            print(f"def {name} : ℚ :=")
            for i, part_name in enumerate(part_names):
                prefix = "  " if i == 0 else "    + "
                print(f"{prefix}{part_name}")

        print("import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25")
        print()
        print("namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")
        print()
        print("open scoped BigOperators")
        print()
        print("open Goldbach")
        print("open Goldbach.BankParams")
        print("open Goldbach.Windows")
        print()
        print(
            f"/- Generated direct-term certificate blocks for tail chunk {chunk_label}, "
            f"subchunk {sub_label}, blocks [{block_start_index},{block_end_index}). -/"
        )
        print()

        for block_index in range(block_start_index, block_end_index):
            block_rel_start = block_index * block_size
            block_support = sub_support[block_rel_start:block_rel_start + block_size]
            block_abs_start = start_idx + sub_start + block_rel_start
            block_abs_end = block_abs_start + len(block_support)
            block_name = f"surrogateDiagTailX0RatChunk{chunk_label}Sub{sub_label}Block{block_index:03d}"
            block_sum_name = f"surrogateDiagonalTailChunk{chunk_label}Sub{sub_label}Block{block_index:03d}Sum"
            block_label = f"TailChunk{chunk_label}Sub{sub_label}Block{block_index:03d}"
            print(
                f"/-- Block {block_index:03d} covers tail-support indices "
                f"[{block_abs_start},{block_abs_end}) and q from {block_support[0]} to {block_support[-1]}. -/"
            )
            print()

            part_names: list[str] = []
            support_names: list[str] = []
            part_totals: list[Fraction] = []

            for part_index, q in enumerate(block_support):
                term_total = surrogate_diagonal_energy_q_rat_cached(
                    X, q, even_window_card, diag_ctx
                )
                part_name = f"{block_name}Part{part_index:03d}"
                support_name = f"{block_label}Part{part_index:03d}SupportExplicit"
                cert_name = f"SurrogateDiagonal{block_label}Part{part_index:03d}CertificateAtX0"
                theorem_name = f"surrogateDiagonal{block_label}Part{part_index:03d}_eq_cert_explicit"
                part_names.append(part_name)
                support_names.append(support_name)
                part_totals.append(term_total)
                print(f"def {support_name} : Finset ℕ :=")
                print(f"  {nat_list_to_lean_finset_literal([q])}")
                print()
                print(f"def {part_name} : ℚ :=")
                print(f"  {qlit(term_total)}")
                print()
                print(f"def {cert_name} : Prop :=")
                print(
                    f"  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 {q}"
                )
                print(f"    = {part_name}")
                print()
                print(f"theorem {theorem_name} :")
                print(f"    {cert_name} →")
                print(f"    (∑ q ∈ {support_name},")
                print("        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
                print(f"      = {part_name} := by")
                print("  intro hcert")
                print(f"  unfold {cert_name} at hcert")
                print(f"  simpa [{support_name}, {part_name}] using hcert")
                print()

            head_parts = list(range(0, min(10, len(part_names))))
            mid_parts = list(range(min(10, len(part_names)), min(20, len(part_names))))
            tail_parts = list(range(min(20, len(part_names)), len(part_names)))

            head_sum_name = f"surrogateDiagonal{block_label}HeadSum"
            mid_sum_name = f"surrogateDiagonal{block_label}MidSum"
            tail_sum_name = f"surrogateDiagonal{block_label}TailSum"
            head_const_name = f"{block_name}Head"
            mid_const_name = f"{block_name}Mid"
            tail_const_name = f"{block_name}Tail"
            head_cert_name = f"SurrogateDiagonal{block_label}HeadCertificateAt"
            mid_cert_name = f"SurrogateDiagonal{block_label}MidCertificateAt"
            tail_cert_name = f"SurrogateDiagonal{block_label}TailCertificateAt"
            arith_name = f"{block_name}_eq_head_add_mid_add_tail"
            block_theorem_name = f"surrogateDiagonal{block_label}_eq_cert_explicit"

            emit_sum_def(head_sum_name, [support_names[i] for i in head_parts])
            print()
            emit_const_def(head_const_name, [part_names[i] for i in head_parts])
            print()
            emit_sum_def(mid_sum_name, [support_names[i] for i in mid_parts])
            print()
            emit_const_def(mid_const_name, [part_names[i] for i in mid_parts])
            print()
            emit_sum_def(tail_sum_name, [support_names[i] for i in tail_parts])
            print()
            emit_const_def(tail_const_name, [part_names[i] for i in tail_parts])
            print()
            print(f"def {block_sum_name} (X0 : ℕ) : ℚ :=")
            print(f"  {head_sum_name} X0")
            print(f"    + {mid_sum_name} X0")
            print(f"    + {tail_sum_name} X0")
            print()
            emit_const_def(block_name, part_names)
            print()
            print(f"theorem {arith_name} :")
            print(f"    {head_const_name} + {mid_const_name} + {tail_const_name} =")
            print(f"      {block_name} := by")
            print(f"  unfold {head_const_name} {mid_const_name} {tail_const_name} {block_name}")
            print("  ring")
            print()
            print(f"def {head_cert_name} (X0 : ℕ) : Prop :=")
            print(f"  {head_sum_name} X0 = {head_const_name}")
            print()
            print(f"def {mid_cert_name} (X0 : ℕ) : Prop :=")
            print(f"  {mid_sum_name} X0 = {mid_const_name}")
            print()
            print(f"def {tail_cert_name} (X0 : ℕ) : Prop :=")
            print(f"  {tail_sum_name} X0 = {tail_const_name}")
            print()
            print(f"theorem {block_theorem_name}")
            print(f"    (hHead : {head_cert_name} X0)")
            print(f"    (hMid : {mid_cert_name} X0)")
            print(f"    (hTail : {tail_cert_name} X0) :")
            print(f"    {block_sum_name} X0 = {block_name} := by")
            print(f"  unfold {head_cert_name} at hHead")
            print(f"  unfold {mid_cert_name} at hMid")
            print(f"  unfold {tail_cert_name} at hTail")
            print(f"  unfold {block_sum_name}")
            print("  rw [hHead, hMid, hTail]")
            print(f"  exact {arith_name}")
            print()

        print("end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")
        return

    if args.emit_diag_tail_rat_subchunks_for_chunk_index >= 0:
        if args.true_series:
            raise SystemExit("--emit-diag-tail-rat-subchunks-for-chunk-index is only implemented for the surrogate normalization")
        chunk_size = max(1, args.diag_tail_chunk_size)
        subchunk_size = max(1, args.diag_tail_subchunk_size)
        tail_support = [
            q for q in support
            if q not in DIAG_MAIN_LOW_Q and q > 50
        ]
        chunk_count = math.ceil(len(tail_support) / chunk_size)
        chunk_index = args.emit_diag_tail_rat_subchunks_for_chunk_index
        if chunk_index >= chunk_count:
            raise SystemExit(
                f"--emit-diag-tail-rat-subchunks-for-chunk-index={chunk_index} out of range for "
                f"{chunk_count} chunks with size {chunk_size}"
            )
        start_idx = chunk_index * chunk_size
        chunk_support = tail_support[start_idx:start_idx + chunk_size]
        chunk_end_idx = start_idx + len(chunk_support)
        chunk_total = Fraction(0, 1)
        subchunk_payloads = []
        started = time.time()
        chunk_label = f"{chunk_index:03d}"
        support_name = (
            "centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000SupportAtX0"
            if chunk_index == 0
            else "centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001SupportAtX0"
        )
        cert_name = (
            "surrogateDiagTailX0RatChunk000"
            if chunk_index == 0
            else "surrogateDiagTailX0RatChunk001"
        )
        theorem_name = (
            "CenteredNormalizedSigmaTruncSurrogateDiagonalTailChunk000RatCertificateAtX0"
            if chunk_index == 0
            else "CenteredNormalizedSigmaTruncSurrogateDiagonalTailChunk001RatCertificateAtX0"
        )
        wrapper_name = (
            "centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000RatCertificateAtX0_of_eq_cert"
            if chunk_index == 0
            else "centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001RatCertificateAtX0_of_eq_cert"
        )
        for subchunk_index, sub_start in enumerate(range(0, len(chunk_support), subchunk_size)):
            sub_support = chunk_support[sub_start:sub_start + subchunk_size]
            sub_total = Fraction(0, 1)
            for q in sub_support:
                sub_total += surrogate_diagonal_energy_q_rat(
                    X, q, mu, phi, even_window, even_window_card
                )
            chunk_total += sub_total
            subchunk_payloads.append(
                (
                    subchunk_index,
                    start_idx + sub_start,
                    start_idx + sub_start + len(sub_support),
                    sub_support[0],
                    sub_support[-1],
                    sub_total,
                )
            )
            if args.progress:
                elapsed = time.time() - started
                print(
                    f"[diag-tail-rat-subchunks] chunk={chunk_index}/{chunk_count} "
                    f"subchunk={subchunk_index + 1}/{math.ceil(len(chunk_support) / subchunk_size)} "
                    f"q={sub_start + len(sub_support)}/{len(chunk_support)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )
        print("import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailSupportBridge")
        print()
        print("namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")
        print()
        print("open scoped BigOperators")
        print()
        print("open Goldbach")
        print("open Goldbach.BankParams")
        print("open Goldbach.Windows")
        print()
        print(
            f"/- Generated chunk-level explicit-support bridge for tail chunk {chunk_label}. -/"
        )
        print()
        subchunk_names = []
        subchunk_support_names = []
        for subchunk_index, abs_start, abs_end, first_q, last_q, sub_total in subchunk_payloads:
            sub_name = f"surrogateDiagTailX0RatChunk{chunk_label}Sub{subchunk_index:03d}"
            sub_support_name = (
                f"centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk{chunk_label}"
                f"Sub{subchunk_index:03d}SupportAtX0"
            )
            subchunk_names.append(sub_name)
            subchunk_support_names.append(sub_support_name)
            print(f"def {sub_name} : ℚ := {fraction_to_q_literal(sub_total)}")
            print(
                f"-- subchunk {subchunk_index:03d} covers tail-support indices [{abs_start},{abs_end}) "
                f"and q from {first_q} to {last_q}"
            )
            print(f"-- support def: {sub_support_name}")
        subchunk_sum_expr = " + ".join(subchunk_names) if subchunk_names else "(0 : ℚ)"
        explicit_chunk_support_name = (
            "TailChunk000SupportExplicit"
            if chunk_index == 0
            else "TailChunk001SupportExplicit"
        )
        if chunk_index == 0:
            explicit_subchunk_sum_names = [
                "TailChunk000Sub000SupportExplicit",
                "TailChunk000Sub001SupportExplicit",
            ]
            explicit_split_name = "TailChunk000SupportExplicit_eq_subchunks"
            explicit_disjoint_name = "TailChunk000SupportExplicit_subchunks_disjoint"
            explicit_sum_name = "surrogateDiagonalTailChunk000ExplicitSupportSum"
            explicit_sum_eq_name = "surrogateDiagTailChunk000_explicitSupport_eq_subchunk_sum"
            explicit_cert_name = "surrogateDiagTailChunk000_explicitSupport_sum_eq_cert"
            main_sum_eq_name = "surrogateDiagTailChunk000_mainSupport_sum_eq_cert"
            main_sum_rewrite_name = "sum_chunk000_over_main_eq_explicit"
            lower_mid = 51
            split_mid = 8269
            upper_mid = 16495
        else:
            explicit_subchunk_sum_names = [
                "TailChunk001Sub000SupportExplicit",
                "TailChunk001Sub001SupportExplicit",
            ]
            explicit_split_name = "TailChunk001SupportExplicit_eq_subchunks"
            explicit_disjoint_name = "TailChunk001SupportExplicit_subchunks_disjoint"
            explicit_sum_name = "surrogateDiagonalTailChunk001ExplicitSupportSum"
            explicit_sum_eq_name = "surrogateDiagTailChunk001_explicitSupport_eq_subchunk_sum"
            explicit_cert_name = "surrogateDiagTailChunk001_explicitSupport_sum_eq_cert"
            main_sum_eq_name = "surrogateDiagTailChunk001_mainSupport_sum_eq_cert"
            main_sum_rewrite_name = "sum_chunk001_over_main_eq_explicit"
            lower_mid = 16496
            split_mid = 24726
            upper_mid = 30000
        print()
        print(f"def {explicit_sum_name} (X0 : ℕ) : ℚ :=")
        print(f"  (∑ q ∈ {explicit_chunk_support_name},")
        print("      surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
        print()
        print(f"theorem {explicit_disjoint_name} :")
        print(f"    Disjoint {explicit_subchunk_sum_names[0]} {explicit_subchunk_sum_names[1]} := by")
        print("  refine Finset.disjoint_left.mpr ?_")
        print("  intro q hq0 hq1")
        print("  rcases Finset.mem_filter.mp hq0 with ⟨hqIcc0, _⟩")
        print("  rcases Finset.mem_filter.mp hq1 with ⟨hqIcc1, _⟩")
        print("  have hle : q ≤ "
              f"{split_mid} := (Finset.mem_Icc.mp hqIcc0).2")
        print("  have hgt : "
              f"{split_mid} < q := by")
        if chunk_index == 0:
            print("    have hlow : 8270 ≤ q := (Finset.mem_Icc.mp hqIcc1).1")
        else:
            print("    have hlow : 24727 ≤ q := (Finset.mem_Icc.mp hqIcc1).1")
        print("    omega")
        print("  omega")
        print()
        print(f"theorem {explicit_split_name} :")
        print(f"    {explicit_chunk_support_name} =")
        print(f"      {explicit_subchunk_sum_names[0]} ∪ {explicit_subchunk_sum_names[1]} := by")
        print(f"  unfold {explicit_chunk_support_name}")
        print(f"    {explicit_subchunk_sum_names[0]}")
        print(f"    {explicit_subchunk_sum_names[1]}")
        print("  apply Finset.ext")
        print("  intro q")
        print("  constructor")
        print("  · intro hq")
        print("    rw [Finset.mem_union]")
        print("    rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩")
        print("    rcases Finset.mem_Icc.mp hqIcc with ⟨hlow, hupp⟩")
        print(f"    by_cases hsplit : q ≤ {split_mid}")
        print("    · left")
        print("      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, hsplit⟩, hsq⟩")
        print("    · right")
        if chunk_index == 0:
            print("      have hsplit' : 8270 ≤ q := by omega")
        else:
            print("      have hsplit' : 24727 ≤ q := by omega")
        print("      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hsplit', hupp⟩, hsq⟩")
        print("  · intro hq")
        print("    rw [Finset.mem_union] at hq")
        print("    rcases hq with hq | hq")
        print("    · rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩")
        print("      rcases Finset.mem_Icc.mp hqIcc with ⟨hlow, _hsplit⟩")
        print("      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlow, by omega⟩, hsq⟩")
        print("    · rcases Finset.mem_filter.mp hq with ⟨hqIcc, hsq⟩")
        print("      rcases Finset.mem_Icc.mp hqIcc with ⟨_hsplit, hupp⟩")
        print("      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hupp⟩, hsq⟩")
        print()
        print(f"theorem {cert_name}_eq_subchunk_sum :")
        print(f"    {subchunk_sum_expr} = {cert_name} := by")
        print(f"  norm_num [{cert_name},")
        for i, name in enumerate(subchunk_names):
            comma = "," if i + 1 < len(subchunk_names) else ""
            print(f"    {name}{comma}")
        print("  ]")
        print()
        print(f"theorem {explicit_sum_eq_name}")
        print("    (hsub000 :")
        print(f"      (∑ q ∈ {explicit_subchunk_sum_names[0]},")
        print("          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
        print(f"        = {subchunk_names[0]})")
        print("    (hsub001 :")
        print(f"      (∑ q ∈ {explicit_subchunk_sum_names[1]},")
        print("          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
        print(f"        = {subchunk_names[1]}) :")
        print(f"    {explicit_sum_name} X0 = {cert_name} := by")
        print(f"  unfold {explicit_sum_name}")
        print(f"  rw [{explicit_split_name}, Finset.sum_union {explicit_disjoint_name}, hsub000, hsub001]")
        print(f"  exact {cert_name}_eq_subchunk_sum")
        print()
        print(f"theorem {main_sum_eq_name}")
        print("    (hsub000 :")
        print(f"      (∑ q ∈ {explicit_subchunk_sum_names[0]},")
        print("          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
        print(f"        = {subchunk_names[0]})")
        print("    (hsub001 :")
        print(f"      (∑ q ∈ {explicit_subchunk_sum_names[1]},")
        print("          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
        print(f"        = {subchunk_names[1]}) :")
        print(f"    (∑ q ∈ {support_name},")
        print("        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =")
        print(f"      {cert_name} := by")
        print(f"  rw [{main_sum_rewrite_name}]")
        print(f"  exact {explicit_cert_name} hsub000 hsub001")
        print()
        print("end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage")
        return

    if args.emit_periodic_main_rat_total:
        if args.true_series:
            raise SystemExit("--emit-periodic-main-rat-total is only implemented for the surrogate normalization")
        ctx = build_surrogate_boundary_exact_context(
            X,
            mu,
            phi,
            spf,
            even_window_card,
            active_support,
            progress=args.progress,
            progress_every_q=max(1, args.progress_every),
        )
        total_rat = Fraction(0, 1)
        active_main_unordered_pairs = 0
        started = time.time()
        total_pairs = len(active_support) * max(len(active_support) - 1, 0) // 2
        processed = 0
        for i, q in enumerate(active_support):
            for q2 in active_support[i + 1:]:
                processed += 1
                val = centered_ramanujan_pair_periodic_main_term_rat_cached(X, q, q2, ctx)
                if val != 0:
                    active_main_unordered_pairs += 1
                    total_rat += 2 * val
                if args.progress and (processed % max(1, args.progress_every) == 0 or processed == total_pairs):
                    elapsed = time.time() - started
                    print(
                        f"[periodic-main-rat] processed={processed}/{total_pairs} "
                        f"active_pairs={active_main_unordered_pairs} elapsed={elapsed:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )
        print("Surrogate periodic-main exact rational total")
        print(f"  X                         = {X}")
        print(f"  active support card       = {len(active_support)}")
        print(f"  active unordered pairs    = {active_main_unordered_pairs}")
        print(f"  rational total numerator  = {total_rat.numerator}")
        print(f"  rational total denominator= {total_rat.denominator}")
        print(f"  Lean ℚ literal            = {fraction_to_q_literal(total_rat)}")
        print(f"  float value               = {float(total_rat):.15f}")
        print("  Lean payload")
        print(f"def surrogatePeriodicMainX0RatCert : ℚ := {fraction_to_q_literal(total_rat)}")
        print()
        print("-- theorem surrogatePeriodicMainRat_X0_eq_cert :")
        print("--     surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0")
        print("--       = surrogatePeriodicMainX0RatCert := by")
        print("--   -- generated certificate proof")
        print()
        print("theorem surrogatePeriodicMainX0RatCert_abs_le_check :")
        print("    |(surrogatePeriodicMainX0RatCert : ℝ)| ≤ surrogatePeriodicMainX0Check.lhs := by")
        print("  norm_num [surrogatePeriodicMainX0RatCert, surrogatePeriodicMainX0Check]")
        return

    if (
        args.boundary_block_key_report
        or args.boundary_skeleton_report
        or args.boundary_pattern_runtime_report
        or args.boundary_family_candidate_report
        or args.boundary_family_residual_report
        or args.boundary_residual_structure_report
        or args.boundary_residual_other_structure_report
        or args.boundary_product_candidate_report
        or args.boundary_pattern_family_exact_topn > 0
        or args.boundary_pattern_product_exact_topn > 0
        or args.boundary_pattern_product_exact_batch
        or args.boundary_pattern_family_exact is not None
        or args.boundary_pattern_family_exact_batch
    ):
        periodic_main_total = 0.0
        active_main_unordered_pairs = 0
        boundary_total = 0.0
    else:
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

    if args.boundary_block_key_report:
        if args.true_series:
            raise SystemExit("--boundary-block-key-report is only implemented for the surrogate normalization")

        block_scope = active_support
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            block_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )
        blocks = list(pair_count_by_block.keys())

        def print_key_family_report(
            label: str,
            key_fn,
        ) -> None:
            counter: Counter[object] = Counter(key_fn(block) for block in blocks)
            distinct = len(counter)
            avg_mult = (len(blocks) / distinct) if distinct else 0.0
            print(f"  {label}")
            print(f"    distinct keys          = {distinct}")
            print(f"    average multiplicity   = {avg_mult:.6f}")
            top_items = sorted(counter.items(), key=lambda kv: (kv[1], kv[0]), reverse=True)[:args.boundary_block_key_top]
            if not top_items:
                print("    top repeated keys      = none")
                return
            print("    top repeated keys")
            for key, mult in top_items:
                print(f"      key={key!r} mult={mult}")

        print("Active boundary block key report")
        print(f"  X                      = {X}")
        print(f"  active support card    = {len(block_scope)}")
        print(f"  active ordered pairs   = {total_pairs}")
        print(f"  distinct blocks        = {len(blocks)}")
        print()
        print_key_family_report("pattern m:n", lambda block: block[0])
        print()
        print_key_family_report("period P", lambda block: 2 * block[1] * block[0][0] * block[0][1])
        print()
        print_key_family_report("pattern + period", lambda block: (block[0], 2 * block[1] * block[0][0] * block[0][1]))
        print()
        print_key_family_report(
            "progression geometry (P, first_even mod P, even_count)",
            lambda block: (
                (P := 2 * block[1] * block[0][0] * block[0][1]),
                boundary_remainder_even_progression(X, block[1] * block[0][0], block[1] * block[0][1])[0] % P,
                boundary_remainder_even_progression(X, block[1] * block[0][0], block[1] * block[0][1])[1],
            ),
        )
        print()
        print_key_family_report(
            "pattern + progression even_count",
            lambda block: (
                block[0],
                boundary_remainder_even_progression(X, block[1] * block[0][0], block[1] * block[0][1])[1],
            ),
        )
        return

    if args.boundary_skeleton_report:
        if args.true_series:
            raise SystemExit("--boundary-skeleton-report is only implemented for the surrogate normalization")

        block_scope = active_support
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            block_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )
        blocks = list(pair_count_by_block.keys())
        odd_rad_cache: dict[int, int] = {}
        v2_cache: dict[int, int] = {}
        prime_support_cache: dict[int, tuple[int, ...]] = {}
        divisor_count_cache: dict[int, int] = {}
        geom_cache: dict[tuple[int, int], tuple[int, int]] = {}

        def g_v2(G: int) -> int:
            if G not in v2_cache:
                v2_cache[G] = v2_adic(G)
            return v2_cache[G]

        def g_odd_rad(G: int) -> int:
            if G not in odd_rad_cache:
                odd_rad_cache[G] = odd_radical_from_spf(G, spf)
            return odd_rad_cache[G]

        def g_prime_support(G: int) -> tuple[int, ...]:
            if G not in prime_support_cache:
                prime_support_cache[G] = prime_support_from_spf(G, spf)
            return prime_support_cache[G]

        def divisor_count(q: int) -> int:
            if q not in divisor_count_cache:
                divisor_count_cache[q] = len(divisors_from_factorization(factorization(q, spf)))
            return divisor_count_cache[q]

        def geom(q: int, q2: int) -> tuple[int, int]:
            key = (q, q2)
            if key not in geom_cache:
                first_even, even_count = boundary_remainder_even_progression(X, q, q2)
                geom_cache[key] = (first_even, even_count)
            return geom_cache[key]

        def print_key_family_report(
            label: str,
            key_fn,
        ) -> None:
            block_counter: Counter[object] = Counter()
            pair_counter: Counter[object] = Counter()
            for block, pair_count in pair_count_by_block.items():
                key = key_fn(block)
                block_counter[key] += 1
                pair_counter[key] += pair_count
            distinct = len(block_counter)
            avg_mult = (len(blocks) / distinct) if distinct else 0.0
            avg_pair_mass = (sum(pair_count_by_block.values()) / distinct) if distinct else 0.0
            print(f"  {label}")
            print(f"    distinct keys          = {distinct}")
            print(f"    average block mult     = {avg_mult:.6f}")
            print(f"    average pair mass      = {avg_pair_mass:.6f}")
            top_items = sorted(
                block_counter.items(),
                key=lambda kv: (kv[1], pair_counter[kv[0]], kv[0]),
                reverse=True,
            )[:args.boundary_skeleton_top]
            if not top_items:
                print("    top repeated keys      = none")
                return
            print("    top repeated keys")
            for key, mult in top_items:
                print(f"      key={key!r} blocks={mult} pair_mass={pair_counter[key]}")

        print("Active boundary skeleton report")
        print(f"  X                      = {X}")
        print(f"  active support card    = {len(block_scope)}")
        print(f"  active ordered pairs   = {total_pairs}")
        print(f"  distinct blocks        = {len(blocks)}")
        print()
        print_key_family_report("pattern m:n", lambda block: block[0])
        print()
        print_key_family_report("G prime support", lambda block: g_prime_support(block[1]))
        print()
        print_key_family_report("G 2-adic + odd radical", lambda block: (g_v2(block[1]), g_odd_rad(block[1])))
        print()
        print_key_family_report("pattern + G skeleton", lambda block: (block[0], g_v2(block[1]), g_odd_rad(block[1])))
        print()
        print_key_family_report(
            "compression signature (pattern, G skeleton, even_count, divisor counts)",
            lambda block: (
                block[0],
                g_v2(block[1]),
                g_odd_rad(block[1]),
                geom(block[1] * block[0][0], block[1] * block[0][1])[1],
                divisor_count(block[1] * block[0][0]),
                divisor_count(block[1] * block[0][1]),
            ),
        )
        return

    if args.boundary_pattern_runtime_report:
        if args.true_series:
            raise SystemExit("--boundary-pattern-runtime-report is only implemented for the surrogate normalization")

        runtime_scope = active_support if args.boundary_pattern_runtime_scope == "active" else support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in runtime_scope}
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            runtime_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        blocks_by_pattern: dict[tuple[int, int], list[tuple[tuple[int, int], int]]] = defaultdict(list)
        pair_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        abs_coeff_proxy_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        for block, pair_count in pair_count_by_block.items():
            pattern, G = block
            q = G * pattern[0]
            q2 = G * pattern[1]
            blocks_by_pattern[pattern].append(block)
            pair_count_by_pattern[pattern] += pair_count
            abs_coeff_proxy_by_pattern[pattern] += abs(coeff_scope[q] * coeff_scope[q2]) * pair_count

        top_patterns = sorted(
            blocks_by_pattern.keys(),
            key=lambda pattern: (
                len(blocks_by_pattern[pattern]),
                pair_count_by_pattern[pattern],
                abs_coeff_proxy_by_pattern[pattern],
                -pattern[0],
                -pattern[1],
            ),
            reverse=True,
        )[:max(args.boundary_pattern_runtime_top, 1)]
        top_pattern_set = set(top_patterns)

        q_needed_exact: set[int] = set()
        selected_block_count = 0
        for pattern in top_patterns:
            for _, G in blocks_by_pattern[pattern]:
                q_needed_exact.add(G * pattern[0])
                q_needed_exact.add(G * pattern[1])
                selected_block_count += 1

        exact_ctx = build_surrogate_boundary_exact_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed_exact),
            progress=args.progress,
            progress_every_q=max(1, args.progress_every),
        )

        signed_by_pattern: dict[tuple[int, int], Fraction] = defaultdict(lambda: Fraction(0, 1))
        abs_by_pattern: dict[tuple[int, int], Fraction] = defaultdict(lambda: Fraction(0, 1))
        elapsed_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        max_elapsed_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        costly_gs_by_pattern: dict[tuple[int, int], list[tuple[float, int, Fraction, Fraction, int]]] = {
            pattern: [] for pattern in top_patterns
        }

        processed = 0
        started = time.time()
        for pattern in top_patterns:
            for _, G in blocks_by_pattern[pattern]:
                q = G * pattern[0]
                q2 = G * pattern[1]
                t0 = time.perf_counter()
                val = 2 * surrogate_boundary_pair_contribution_rat_cached(X, q, q2, exact_ctx)
                elapsed = time.perf_counter() - t0
                abs_val = abs(val)
                signed_by_pattern[pattern] += val
                abs_by_pattern[pattern] += abs_val
                elapsed_by_pattern[pattern] += elapsed
                max_elapsed_by_pattern[pattern] = max(max_elapsed_by_pattern[pattern], elapsed)
                entry = (elapsed, G, val, abs_val, pair_count_by_block[(pattern, G)])
                costly = costly_gs_by_pattern[pattern]
                costly.append(entry)
                costly.sort(key=lambda rec: (rec[0], abs(float(rec[3])), rec[1]), reverse=True)
                del costly[max(args.boundary_pattern_runtime_top_g, 0):]
                processed += 1
                if args.progress and processed % max(1, min(args.progress_every, 1000)) == 0:
                    elapsed_total = time.time() - started
                    print(
                        f"[boundary-pattern-runtime] processed_blocks={processed}/{selected_block_count} "
                        f"patterns={len(top_pattern_set)} elapsed={elapsed_total:.1f}s",
                        file=sys.stderr,
                        flush=True,
                    )

        print("Active boundary pattern runtime report")
        print(f"  X                         = {X}")
        print(f"  scope                     = {args.boundary_pattern_runtime_scope}")
        print(f"  support card              = {len(runtime_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  distinct active blocks    = {len(pair_count_by_block)}")
        print(f"  evaluated top patterns    = {len(top_patterns)}")
        print(f"  evaluated selected blocks = {selected_block_count}")
        print()
        print("  pattern   G-count   pair mass     abs coeff proxy      exact signed         exact abs            ratio     avg ms/G   max ms/G")
        for pattern in top_patterns:
            g_count = len(blocks_by_pattern[pattern])
            signed = signed_by_pattern[pattern]
            abs_mass = abs_by_pattern[pattern]
            ratio = (abs(float(signed)) / float(abs_mass)) if abs_mass else 0.0
            avg_ms = 1000.0 * elapsed_by_pattern[pattern] / max(g_count, 1)
            max_ms = 1000.0 * max_elapsed_by_pattern[pattern]
            print(
                f"  {pattern[0]}:{pattern[1]:<5} {g_count:>8}  {pair_count_by_pattern[pattern]:>10}  "
                f"{abs_coeff_proxy_by_pattern[pattern]:> .12e}  {float(signed):> .12e}  "
                f"{float(abs_mass):> .12e}  {ratio:> .6f}  {avg_ms:>9.3f}  {max_ms:>9.3f}"
            )
            for elapsed, G, val, abs_val, pair_count in costly_gs_by_pattern[pattern]:
                print(
                    f"    G={G:<8d} pair_mass={pair_count:<3d} elapsed_ms={1000.0 * elapsed:>9.3f} "
                    f"signed={float(val):> .12e} abs={float(abs_val):> .12e}"
                )
        return

    if args.boundary_family_candidate_report:
        if args.true_series:
            raise SystemExit("--boundary-family-candidate-report is only implemented for the surrogate normalization")

        excluded_patterns = parse_selected_patterns(args.exclude_families)
        excluded_products = parse_selected_products(args.exclude_products)
        excluded_products = parse_selected_products(args.exclude_products)
        candidate_scope = active_support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in candidate_scope}
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            candidate_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        pair_mass_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        abs_coeff_proxy_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        runtime_proxy_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        divisor_count_cache: dict[int, int] = {}

        def divisor_count(q: int) -> int:
            if q not in divisor_count_cache:
                divisor_count_cache[q] = len(divisors_from_factorization(factorization(q, spf)))
            return divisor_count_cache[q]

        for block, pair_mass in pair_count_by_block.items():
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            block_count_by_pattern[pattern] += 1
            pair_mass_by_pattern[pattern] += pair_mass
            abs_coeff_proxy_by_pattern[pattern] += abs(coeff_scope[q] * coeff_scope[q2]) * pair_mass
            runtime_proxy_by_pattern[pattern] += divisor_count(q) * divisor_count(q2)

        top_k = max(args.boundary_family_candidate_top, 1)
        candidate_k = (
            max(args.boundary_family_candidate_patterns, top_k)
            if args.boundary_family_candidate_patterns > 0
            else max(top_k * 10, top_k)
        )
        candidate_patterns = sorted(
            block_count_by_pattern.keys(),
            key=lambda pat: (
                abs_coeff_proxy_by_pattern[pat],
                runtime_proxy_by_pattern[pat],
                pair_mass_by_pattern[pat],
                block_count_by_pattern[pat],
                -pat[0],
                -pat[1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_pattern_set = set(candidate_patterns)

        q_needed: set[int] = set()
        for block in pair_count_by_block:
            pattern, G = block
            if pattern in candidate_pattern_set:
                q_needed.add(G * pattern[0])
                q_needed.add(G * pattern[1])

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        abs_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for block in pair_count_by_block:
            pattern, G = block
            if pattern not in candidate_pattern_set:
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            signed_float_by_pattern[pattern] += val
            abs_float_by_pattern[pattern] += abs(val)
            processed += 1
            if args.progress and processed % max(1, min(args.progress_every, 1000)) == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-family-candidate] processed_blocks={processed} "
                    f"candidate_patterns={len(candidate_pattern_set)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        top_negative = sorted(
            candidate_patterns,
            key=lambda pat: (signed_float_by_pattern[pat], -abs_float_by_pattern[pat]),
        )[:top_k]
        top_abs = sorted(
            candidate_patterns,
            key=lambda pat: (abs_float_by_pattern[pat], abs(signed_float_by_pattern[pat]), runtime_proxy_by_pattern[pat]),
            reverse=True,
        )[:top_k]
        top_runtime = sorted(
            candidate_patterns,
            key=lambda pat: (runtime_proxy_by_pattern[pat], abs_float_by_pattern[pat], pair_mass_by_pattern[pat]),
            reverse=True,
        )[:top_k]

        def print_table(title: str, pats: list[tuple[int, int]]) -> None:
            print(title)
            print("  pattern   G-count   pair mass     float signed         float abs            ratio     runtime proxy      abs coeff proxy")
            for pat in pats:
                signed = signed_float_by_pattern[pat]
                abs_mass = abs_float_by_pattern[pat]
                ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
                print(
                    f"  {pat[0]}:{pat[1]:<5} {block_count_by_pattern[pat]:>8}  {pair_mass_by_pattern[pat]:>10}  "
                    f"{signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}  "
                    f"{runtime_proxy_by_pattern[pat]:>13}  {abs_coeff_proxy_by_pattern[pat]:> .12e}"
                )
            print()

        print("Active boundary family candidate report")
        print(f"  X                         = {X}")
        print(f"  support card              = {len(candidate_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  excluded patterns         = {sorted(excluded_patterns)}")
        print(f"  excluded products         = {sorted(excluded_products)}")
        print(f"  candidate patterns eval   = {len(candidate_patterns)}")
        print()
        print_table("Top unevaluated families by negative signed float", top_negative)
        print_table("Top unevaluated families by absolute float mass", top_abs)
        print_table("Top unevaluated families by runtime proxy", top_runtime)
        return

    if args.boundary_family_residual_report:
        if args.true_series:
            raise SystemExit("--boundary-family-residual-report is only implemented for the surrogate normalization")

        excluded_patterns = parse_selected_patterns(args.exclude_families)
        excluded_products = parse_selected_products(args.exclude_products)
        candidate_scope = active_support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in candidate_scope}
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            candidate_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        pair_mass_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        abs_coeff_proxy_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        runtime_proxy_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        divisor_count_cache: dict[int, int] = {}

        def divisor_count(q: int) -> int:
            if q not in divisor_count_cache:
                divisor_count_cache[q] = len(divisors_from_factorization(factorization(q, spf)))
            return divisor_count_cache[q]

        for block, pair_mass in pair_count_by_block.items():
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            block_count_by_pattern[pattern] += 1
            pair_mass_by_pattern[pattern] += pair_mass
            abs_coeff_proxy_by_pattern[pattern] += abs(coeff_scope[q] * coeff_scope[q2]) * pair_mass
            runtime_proxy_by_pattern[pattern] += divisor_count(q) * divisor_count(q2)

        top_k = max(args.boundary_family_candidate_top, 1)
        candidate_k = (
            max(args.boundary_family_candidate_patterns, top_k)
            if args.boundary_family_candidate_patterns > 0
            else max(top_k * 10, top_k)
        )
        tracked_patterns = sorted(
            block_count_by_pattern.keys(),
            key=lambda pat: (
                abs_coeff_proxy_by_pattern[pat],
                runtime_proxy_by_pattern[pat],
                pair_mass_by_pattern[pat],
                block_count_by_pattern[pat],
                -pat[0],
                -pat[1],
            ),
            reverse=True,
        )[:candidate_k]
        tracked_pattern_set = set(tracked_patterns)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(candidate_scope),
            progress=args.progress,
        )

        tracked_signed_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        tracked_abs_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        remaining_signed_total = 0.0
        remaining_abs_total = 0.0
        processed = 0
        started = time.time()
        for block in pair_count_by_block:
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            remaining_signed_total += val
            remaining_abs_total += abs(val)
            if pattern in tracked_pattern_set:
                tracked_signed_by_pattern[pattern] += val
                tracked_abs_by_pattern[pattern] += abs(val)
            processed += 1
            if args.progress and processed % max(1, min(args.progress_every, 20000)) == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-family-residual] processed_blocks={processed}/{len(pair_count_by_block)} "
                    f"tracked_patterns={len(tracked_pattern_set)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        tracked_negative = sorted(
            tracked_patterns,
            key=lambda pat: (tracked_signed_by_pattern[pat], -tracked_abs_by_pattern[pat]),
        )[:top_k]
        tracked_positive = sorted(
            tracked_patterns,
            key=lambda pat: (tracked_signed_by_pattern[pat], tracked_abs_by_pattern[pat]),
            reverse=True,
        )[:top_k]
        tracked_abs = sorted(
            tracked_patterns,
            key=lambda pat: (tracked_abs_by_pattern[pat], abs(tracked_signed_by_pattern[pat]), runtime_proxy_by_pattern[pat]),
            reverse=True,
        )[:top_k]

        def print_table(title: str, pats: list[tuple[int, int]]) -> None:
            print(title)
            print("  pattern   G-count   pair mass     float signed         float abs            ratio     runtime proxy      abs coeff proxy")
            for pat in pats:
                signed = tracked_signed_by_pattern[pat]
                abs_mass = tracked_abs_by_pattern[pat]
                ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
                print(
                    f"  {pat[0]}:{pat[1]:<5} {block_count_by_pattern[pat]:>8}  {pair_mass_by_pattern[pat]:>10}  "
                    f"{signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}  "
                    f"{runtime_proxy_by_pattern[pat]:>13}  {abs_coeff_proxy_by_pattern[pat]:> .12e}"
                )
            print()

        print("Active boundary residual family report")
        print(f"  X                         = {X}")
        print(f"  support card              = {len(candidate_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  excluded patterns         = {sorted(excluded_patterns)}")
        print(f"  excluded products         = {sorted(excluded_products)}")
        print(f"  tracked patterns eval     = {len(tracked_patterns)}")
        print(f"  remaining float signed    = {remaining_signed_total:.12e}")
        print(f"  remaining float abs       = {remaining_abs_total:.12e}")
        print(f"  remaining ratio           = {(abs(remaining_signed_total) / remaining_abs_total) if remaining_abs_total else 0.0:.6f}")
        print()
        print_table("Top remaining tracked families by positive signed float", tracked_positive)
        print_table("Top remaining tracked families by negative signed float", tracked_negative)
        print_table("Top remaining tracked families by absolute float mass", tracked_abs)
        return

    if args.boundary_residual_structure_report:
        if args.true_series:
            raise SystemExit("--boundary-residual-structure-report is only implemented for the surrogate normalization")

        excluded_patterns = parse_selected_patterns(args.exclude_families)
        excluded_products = parse_selected_products(args.exclude_products)
        candidate_scope = active_support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in candidate_scope}
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            candidate_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        pair_mass_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        runtime_proxy_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        divisor_count_cache: dict[int, int] = {}

        def divisor_count(q: int) -> int:
            if q not in divisor_count_cache:
                divisor_count_cache[q] = len(divisors_from_factorization(factorization(q, spf)))
            return divisor_count_cache[q]

        for block, pair_mass in pair_count_by_block.items():
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            block_count_by_pattern[pattern] += 1
            pair_mass_by_pattern[pattern] += pair_mass
            runtime_proxy_by_pattern[pattern] += divisor_count(q) * divisor_count(q2)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(candidate_scope),
            progress=args.progress,
        )

        numerator_signed: dict[int, float] = defaultdict(float)
        numerator_abs: dict[int, float] = defaultdict(float)
        dyadic_signed: dict[tuple[int, int], float] = defaultdict(float)
        dyadic_abs: dict[tuple[int, int], float] = defaultdict(float)
        bucket_signed: dict[str, float] = defaultdict(float)
        bucket_abs: dict[str, float] = defaultdict(float)
        class_signed: dict[str, float] = defaultdict(float)
        class_abs: dict[str, float] = defaultdict(float)
        remaining_signed_total = 0.0
        remaining_abs_total = 0.0

        def odd_part(n: int) -> int:
            while n % 2 == 0:
                n //= 2
            return n

        bucket_width = max(args.boundary_residual_denominator_bucket, 1)

        def numerator_class(m: int) -> str:
            if m in (1, 3, 5, 7, 10):
                return str(m)
            return "other"

        processed = 0
        started = time.time()
        for block in pair_count_by_block:
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            abs_val = abs(val)
            m, n = pattern
            numerator_signed[m] += val
            numerator_abs[m] += abs_val
            dyadic_key = (odd_part(m), odd_part(n))
            dyadic_signed[dyadic_key] += val
            dyadic_abs[dyadic_key] += abs_val
            lo = ((n - 1) // bucket_width) * bucket_width + 1
            hi = lo + bucket_width - 1
            bucket_key = f"{lo:03d}-{hi:03d}"
            bucket_signed[bucket_key] += val
            bucket_abs[bucket_key] += abs_val
            cls = numerator_class(m)
            class_signed[cls] += val
            class_abs[cls] += abs_val
            remaining_signed_total += val
            remaining_abs_total += abs_val
            processed += 1
            if args.progress and processed % max(1, min(args.progress_every, 20000)) == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-residual-structure] processed_blocks={processed}/{len(pair_count_by_block)} "
                    f"elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        numerator_family_count: dict[int, int] = defaultdict(int)
        numerator_block_count: dict[int, int] = defaultdict(int)
        numerator_pair_mass: dict[int, int] = defaultdict(int)
        numerator_runtime: dict[int, int] = defaultdict(int)
        dyadic_family_count: dict[tuple[int, int], int] = defaultdict(int)
        dyadic_block_count: dict[tuple[int, int], int] = defaultdict(int)
        dyadic_pair_mass: dict[tuple[int, int], int] = defaultdict(int)
        dyadic_runtime: dict[tuple[int, int], int] = defaultdict(int)
        bucket_family_count: dict[str, int] = defaultdict(int)
        bucket_block_count: dict[str, int] = defaultdict(int)
        bucket_pair_mass: dict[str, int] = defaultdict(int)
        bucket_runtime: dict[str, int] = defaultdict(int)
        class_family_count: dict[str, int] = defaultdict(int)
        class_block_count: dict[str, int] = defaultdict(int)
        class_pair_mass: dict[str, int] = defaultdict(int)
        class_runtime: dict[str, int] = defaultdict(int)

        for pattern in block_count_by_pattern:
            m, n = pattern
            dyadic_key = (odd_part(m), odd_part(n))
            lo = ((n - 1) // bucket_width) * bucket_width + 1
            hi = lo + bucket_width - 1
            bucket_key = f"{lo:03d}-{hi:03d}"
            cls = numerator_class(m)

            numerator_family_count[m] += 1
            numerator_block_count[m] += block_count_by_pattern[pattern]
            numerator_pair_mass[m] += pair_mass_by_pattern[pattern]
            numerator_runtime[m] += runtime_proxy_by_pattern[pattern]

            dyadic_family_count[dyadic_key] += 1
            dyadic_block_count[dyadic_key] += block_count_by_pattern[pattern]
            dyadic_pair_mass[dyadic_key] += pair_mass_by_pattern[pattern]
            dyadic_runtime[dyadic_key] += runtime_proxy_by_pattern[pattern]

            bucket_family_count[bucket_key] += 1
            bucket_block_count[bucket_key] += block_count_by_pattern[pattern]
            bucket_pair_mass[bucket_key] += pair_mass_by_pattern[pattern]
            bucket_runtime[bucket_key] += runtime_proxy_by_pattern[pattern]

            class_family_count[cls] += 1
            class_block_count[cls] += block_count_by_pattern[pattern]
            class_pair_mass[cls] += pair_mass_by_pattern[pattern]
            class_runtime[cls] += runtime_proxy_by_pattern[pattern]

        top_k = max(args.boundary_residual_structure_top, 1)

        def top_keys(abs_map: dict[object, float]) -> list[object]:
            return sorted(abs_map.keys(), key=lambda key: (abs_map[key], abs(abs_map[key])), reverse=True)[:top_k]

        def print_group_table(
            title: str,
            keys: list[object],
            signed_map: dict[object, float],
            abs_map: dict[object, float],
            family_count_map: dict[object, int],
            block_count_map: dict[object, int],
            pair_mass_map: dict[object, int],
            runtime_map: dict[object, int],
            key_fmt,
        ) -> None:
            print(title)
            print("  group                 signed              abs            ratio   families   G-count   pair mass   runtime proxy")
            for key in keys:
                signed = signed_map[key]
                abs_mass = abs_map[key]
                ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
                print(
                    f"  {key_fmt(key):<18} {signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}"
                    f"  {family_count_map[key]:>8}  {block_count_map[key]:>8}  {pair_mass_map[key]:>10}  {runtime_map[key]:>13}"
                )
            print()

        print("Active boundary residual structure report")
        print(f"  X                         = {X}")
        print(f"  support card              = {len(candidate_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  excluded patterns         = {sorted(excluded_patterns)}")
        print(f"  excluded products         = {sorted(excluded_products)}")
        print(f"  remaining float signed    = {remaining_signed_total:.12e}")
        print(f"  remaining float abs       = {remaining_abs_total:.12e}")
        print(f"  remaining ratio           = {(abs(remaining_signed_total) / remaining_abs_total) if remaining_abs_total else 0.0:.6f}")
        print()
        print_group_table(
            "Top residual groups by numerator m",
            top_keys(numerator_abs),
            numerator_signed,
            numerator_abs,
            numerator_family_count,
            numerator_block_count,
            numerator_pair_mass,
            numerator_runtime,
            lambda key: f"m={key}",
        )
        print_group_table(
            "Top residual groups by dyadic orbit",
            top_keys(dyadic_abs),
            dyadic_signed,
            dyadic_abs,
            dyadic_family_count,
            dyadic_block_count,
            dyadic_pair_mass,
            dyadic_runtime,
            lambda key: f"({key[0]},{key[1]})",
        )
        print_group_table(
            "Top residual groups by denominator bucket",
            top_keys(bucket_abs),
            bucket_signed,
            bucket_abs,
            bucket_family_count,
            bucket_block_count,
            bucket_pair_mass,
            bucket_runtime,
            lambda key: key,
        )
        print_group_table(
            "Residual by small-numerator class",
            sorted(class_abs.keys(), key=lambda key: (class_abs[key], abs(class_signed[key])), reverse=True),
            class_signed,
            class_abs,
            class_family_count,
            class_block_count,
            class_pair_mass,
            class_runtime,
            lambda key: key,
        )
        return

    if args.boundary_residual_other_structure_report:
        if args.true_series:
            raise SystemExit("--boundary-residual-other-structure-report is only implemented for the surrogate normalization")

        excluded_patterns = parse_selected_patterns(args.exclude_families)
        excluded_products = parse_selected_products(args.exclude_products)
        candidate_scope = active_support
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            candidate_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        pair_mass_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        runtime_proxy_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        divisor_count_cache: dict[int, int] = {}

        def divisor_count(q: int) -> int:
            if q not in divisor_count_cache:
                divisor_count_cache[q] = len(divisors_from_factorization(factorization(q, spf)))
            return divisor_count_cache[q]

        for block, pair_mass in pair_count_by_block.items():
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            block_count_by_pattern[pattern] += 1
            pair_mass_by_pattern[pattern] += pair_mass
            runtime_proxy_by_pattern[pattern] += divisor_count(q) * divisor_count(q2)

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(candidate_scope),
            progress=args.progress,
        )

        bucket_width = max(args.boundary_residual_denominator_bucket, 1)

        def odd_part(n: int) -> int:
            while n % 2 == 0:
                n //= 2
            return n

        def numerator_class(m: int) -> str:
            if m in (1, 3, 5, 7, 10):
                return str(m)
            return "other"

        def smallest_prime_factor(n: int) -> int:
            return spf[n] if n > 1 else 1

        other_signed_total = 0.0
        other_abs_total = 0.0

        orbit_bucket_signed: dict[tuple[tuple[int, int], str], float] = defaultdict(float)
        orbit_bucket_abs: dict[tuple[tuple[int, int], str], float] = defaultdict(float)
        orbit_bucket_family_count: dict[tuple[tuple[int, int], str], int] = defaultdict(int)
        orbit_bucket_block_count: dict[tuple[tuple[int, int], str], int] = defaultdict(int)
        orbit_bucket_pair_mass: dict[tuple[tuple[int, int], str], int] = defaultdict(int)
        orbit_bucket_runtime: dict[tuple[tuple[int, int], str], int] = defaultdict(int)

        spf_pair_signed: dict[tuple[int, int], float] = defaultdict(float)
        spf_pair_abs: dict[tuple[int, int], float] = defaultdict(float)
        spf_pair_family_count: dict[tuple[int, int], int] = defaultdict(int)
        spf_pair_block_count: dict[tuple[int, int], int] = defaultdict(int)
        spf_pair_pair_mass: dict[tuple[int, int], int] = defaultdict(int)
        spf_pair_runtime: dict[tuple[int, int], int] = defaultdict(int)

        product_signed: dict[int, float] = defaultdict(float)
        product_abs: dict[int, float] = defaultdict(float)
        product_family_count: dict[int, int] = defaultdict(int)
        product_block_count: dict[int, int] = defaultdict(int)
        product_pair_mass: dict[int, int] = defaultdict(int)
        product_runtime: dict[int, int] = defaultdict(int)

        seen_patterns: set[tuple[int, int]] = set()
        processed = 0
        started = time.time()
        for block in pair_count_by_block:
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            m, n = pattern
            if numerator_class(m) != "other":
                continue
            q = G * m
            q2 = G * n
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            abs_val = abs(val)
            other_signed_total += val
            other_abs_total += abs_val

            orbit = (odd_part(m), odd_part(n))
            lo = ((n - 1) // bucket_width) * bucket_width + 1
            hi = lo + bucket_width - 1
            bucket_key = f"{lo:03d}-{hi:03d}"
            orbit_bucket_key = (orbit, bucket_key)
            orbit_bucket_signed[orbit_bucket_key] += val
            orbit_bucket_abs[orbit_bucket_key] += abs_val

            spf_key = (smallest_prime_factor(m), smallest_prime_factor(n))
            spf_pair_signed[spf_key] += val
            spf_pair_abs[spf_key] += abs_val

            prod = m * n
            product_signed[prod] += val
            product_abs[prod] += abs_val

            if pattern not in seen_patterns:
                seen_patterns.add(pattern)
                orbit_bucket_family_count[orbit_bucket_key] += 1
                orbit_bucket_block_count[orbit_bucket_key] += block_count_by_pattern[pattern]
                orbit_bucket_pair_mass[orbit_bucket_key] += pair_mass_by_pattern[pattern]
                orbit_bucket_runtime[orbit_bucket_key] += runtime_proxy_by_pattern[pattern]

                spf_pair_family_count[spf_key] += 1
                spf_pair_block_count[spf_key] += block_count_by_pattern[pattern]
                spf_pair_pair_mass[spf_key] += pair_mass_by_pattern[pattern]
                spf_pair_runtime[spf_key] += runtime_proxy_by_pattern[pattern]

                product_family_count[prod] += 1
                product_block_count[prod] += block_count_by_pattern[pattern]
                product_pair_mass[prod] += pair_mass_by_pattern[pattern]
                product_runtime[prod] += runtime_proxy_by_pattern[pattern]

            processed += 1
            if args.progress and processed % max(1, min(args.progress_every, 20000)) == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-residual-other-structure] processed_blocks={processed}/{len(pair_count_by_block)} "
                    f"elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        top_k = max(args.boundary_residual_structure_top, 1)

        def top_keys(abs_map: dict[object, float]) -> list[object]:
            return sorted(abs_map.keys(), key=lambda key: (abs_map[key], abs(abs_map[key])), reverse=True)[:top_k]

        def print_group_table(
            title: str,
            keys: list[object],
            signed_map: dict[object, float],
            abs_map: dict[object, float],
            family_count_map: dict[object, int],
            block_count_map: dict[object, int],
            pair_mass_map: dict[object, int],
            runtime_map: dict[object, int],
            key_fmt,
        ) -> None:
            print(title)
            print("  group                           signed              abs            ratio   families   G-count   pair mass   runtime proxy")
            for key in keys:
                signed = signed_map[key]
                abs_mass = abs_map[key]
                ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
                print(
                    f"  {key_fmt(key):<30} {signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}"
                    f"  {family_count_map[key]:>8}  {block_count_map[key]:>8}  {pair_mass_map[key]:>10}  {runtime_map[key]:>13}"
                )
            print()

        print("Active boundary residual OTHER-bucket structure report")
        print(f"  X                         = {X}")
        print(f"  support card              = {len(candidate_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  excluded patterns         = {sorted(excluded_patterns)}")
        print(f"  excluded products         = {sorted(excluded_products)}")
        print(f"  other float signed        = {other_signed_total:.12e}")
        print(f"  other float abs           = {other_abs_total:.12e}")
        print(f"  other ratio               = {(abs(other_signed_total) / other_abs_total) if other_abs_total else 0.0:.6f}")
        print()
        print_group_table(
            "Top OTHER groups by (dyadic orbit, denominator bucket)",
            top_keys(orbit_bucket_abs),
            orbit_bucket_signed,
            orbit_bucket_abs,
            orbit_bucket_family_count,
            orbit_bucket_block_count,
            orbit_bucket_pair_mass,
            orbit_bucket_runtime,
            lambda key: f"{key[0]} @ {key[1]}",
        )
        print_group_table(
            "Top OTHER groups by (spf(m), spf(n))",
            top_keys(spf_pair_abs),
            spf_pair_signed,
            spf_pair_abs,
            spf_pair_family_count,
            spf_pair_block_count,
            spf_pair_pair_mass,
            spf_pair_runtime,
            lambda key: f"({key[0]},{key[1]})",
        )
        print_group_table(
            "Top OTHER groups by product m*n",
            top_keys(product_abs),
            product_signed,
            product_abs,
            product_family_count,
            product_block_count,
            product_pair_mass,
            product_runtime,
            lambda key: f"{key}",
        )
        return

    if args.boundary_product_candidate_report:
        if args.true_series:
            raise SystemExit("--boundary-product-candidate-report is only implemented for the surrogate normalization")

        excluded_patterns = parse_selected_patterns(args.exclude_families)
        excluded_products = parse_selected_products(args.exclude_products)
        candidate_scope = active_support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in candidate_scope}
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            candidate_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        pair_mass_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        abs_coeff_proxy_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        runtime_proxy_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        divisor_count_cache: dict[int, int] = {}

        def divisor_count(q: int) -> int:
            if q not in divisor_count_cache:
                divisor_count_cache[q] = len(divisors_from_factorization(factorization(q, spf)))
            return divisor_count_cache[q]

        for block, pair_mass in pair_count_by_block.items():
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            block_count_by_pattern[pattern] += 1
            pair_mass_by_pattern[pattern] += pair_mass
            abs_coeff_proxy_by_pattern[pattern] += abs(coeff_scope[q] * coeff_scope[q2]) * pair_mass
            runtime_proxy_by_pattern[pattern] += divisor_count(q) * divisor_count(q2)

        top_k = max(args.boundary_family_candidate_top, 1)
        candidate_k = (
            max(args.boundary_family_candidate_patterns, top_k)
            if args.boundary_family_candidate_patterns > 0
            else max(top_k * 10, top_k)
        )
        candidate_patterns = sorted(
            block_count_by_pattern.keys(),
            key=lambda pat: (
                abs_coeff_proxy_by_pattern[pat],
                runtime_proxy_by_pattern[pat],
                pair_mass_by_pattern[pat],
                block_count_by_pattern[pat],
                -pat[0],
                -pat[1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_pattern_set = set(candidate_patterns)

        q_needed: set[int] = set()
        for block in pair_count_by_block:
            pattern, G = block
            if pattern in candidate_pattern_set:
                q_needed.add(G * pattern[0])
                q_needed.add(G * pattern[1])

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        abs_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for block in pair_count_by_block:
            pattern, G = block
            if pattern not in candidate_pattern_set:
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            signed_float_by_pattern[pattern] += val
            abs_float_by_pattern[pattern] += abs(val)
            processed += 1
            if args.progress and processed % max(1, min(args.progress_every, 1000)) == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-product-candidate] processed_blocks={processed} "
                    f"candidate_patterns={len(candidate_pattern_set)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        patterns_by_product: dict[int, list[tuple[int, int]]] = defaultdict(list)
        block_count_by_product: dict[int, int] = defaultdict(int)
        pair_mass_by_product: dict[int, int] = defaultdict(int)
        runtime_proxy_by_product: dict[int, int] = defaultdict(int)
        abs_coeff_proxy_by_product: dict[int, float] = defaultdict(float)
        signed_float_by_product: dict[int, float] = defaultdict(float)
        abs_float_by_product: dict[int, float] = defaultdict(float)

        for pattern in candidate_patterns:
            prod = pattern[0] * pattern[1]
            patterns_by_product[prod].append(pattern)
            block_count_by_product[prod] += block_count_by_pattern[pattern]
            pair_mass_by_product[prod] += pair_mass_by_pattern[pattern]
            runtime_proxy_by_product[prod] += runtime_proxy_by_pattern[pattern]
            abs_coeff_proxy_by_product[prod] += abs_coeff_proxy_by_pattern[pattern]
            signed_float_by_product[prod] += signed_float_by_pattern[pattern]
            abs_float_by_product[prod] += abs_float_by_pattern[pattern]

        products = list(patterns_by_product.keys())
        top_negative = sorted(products, key=lambda p: (signed_float_by_product[p], -abs_float_by_product[p]))[:top_k]
        top_positive = sorted(products, key=lambda p: (signed_float_by_product[p], abs_float_by_product[p]), reverse=True)[:top_k]
        top_abs = sorted(products, key=lambda p: (abs_float_by_product[p], abs(signed_float_by_product[p]), runtime_proxy_by_product[p]), reverse=True)[:top_k]

        def print_table(title: str, prods: list[int]) -> None:
            print(title)
            print("  product  fams   G-count   pair mass     float signed         float abs            ratio     runtime proxy      abs coeff proxy")
            for prod in prods:
                signed = signed_float_by_product[prod]
                abs_mass = abs_float_by_product[prod]
                ratio = (abs(signed) / abs_mass) if abs_mass else 0.0
                print(
                    f"  {prod:<7d} {len(patterns_by_product[prod]):>4}  {block_count_by_product[prod]:>8}  {pair_mass_by_product[prod]:>10}  "
                    f"{signed:> .12e}  {abs_mass:> .12e}  {ratio:> .6f}  "
                    f"{runtime_proxy_by_product[prod]:>13}  {abs_coeff_proxy_by_product[prod]:> .12e}"
                )
                members = ' '.join(f"{a}:{b}" for (a, b) in sorted(patterns_by_product[prod]))
                print(f"    members: {members}")
            print()

        print("Active boundary product-class candidate report")
        print(f"  X                         = {X}")
        print(f"  support card              = {len(candidate_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  excluded patterns         = {sorted(excluded_patterns)}")
        print(f"  excluded products         = {sorted(excluded_products)}")
        print(f"  candidate patterns eval   = {len(candidate_patterns)}")
        print(f"  grouped products          = {len(products)}")
        print()
        print_table("Top unevaluated product classes by positive signed float", top_positive)
        print_table("Top unevaluated product classes by negative signed float", top_negative)
        print_table("Top unevaluated product classes by absolute float mass", top_abs)
        return

    if args.boundary_pattern_family_exact_topn > 0:
        if args.true_series:
            raise SystemExit("--boundary-pattern-family-exact-topn is only implemented for the surrogate normalization")

        excluded_patterns = parse_selected_patterns(args.exclude_families)
        excluded_products = parse_selected_products(args.exclude_products)
        candidate_scope = active_support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in candidate_scope}
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            candidate_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        pair_mass_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        abs_coeff_proxy_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        runtime_proxy_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        divisor_count_cache: dict[int, int] = {}

        def divisor_count(q: int) -> int:
            if q not in divisor_count_cache:
                divisor_count_cache[q] = len(divisors_from_factorization(factorization(q, spf)))
            return divisor_count_cache[q]

        for block, pair_mass in pair_count_by_block.items():
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            block_count_by_pattern[pattern] += 1
            pair_mass_by_pattern[pattern] += pair_mass
            abs_coeff_proxy_by_pattern[pattern] += abs(coeff_scope[q] * coeff_scope[q2]) * pair_mass
            runtime_proxy_by_pattern[pattern] += divisor_count(q) * divisor_count(q2)

        top_k = max(args.boundary_pattern_family_exact_topn, 1)
        candidate_k = (
            max(args.boundary_family_candidate_patterns, top_k)
            if args.boundary_family_candidate_patterns > 0
            else max(top_k * 10, top_k)
        )
        candidate_patterns = sorted(
            block_count_by_pattern.keys(),
            key=lambda pat: (
                abs_coeff_proxy_by_pattern[pat],
                runtime_proxy_by_pattern[pat],
                pair_mass_by_pattern[pat],
                block_count_by_pattern[pat],
                -pat[0],
                -pat[1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_pattern_set = set(candidate_patterns)

        q_needed: set[int] = set()
        for block in pair_count_by_block:
            pattern, G = block
            if pattern in candidate_pattern_set:
                q_needed.add(G * pattern[0])
                q_needed.add(G * pattern[1])

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        abs_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for block in pair_count_by_block:
            pattern, G = block
            if pattern not in candidate_pattern_set:
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            signed_float_by_pattern[pattern] += val
            abs_float_by_pattern[pattern] += abs(val)
            processed += 1
            if args.progress and processed % max(1, min(args.progress_every, 1000)) == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-family-topn] processed_blocks={processed} "
                    f"candidate_patterns={len(candidate_pattern_set)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        if args.boundary_pattern_family_topn_order == "negative":
            selected_patterns = sorted(
                candidate_patterns,
                key=lambda pat: (signed_float_by_pattern[pat], -abs_float_by_pattern[pat]),
            )[:top_k]
        elif args.boundary_pattern_family_topn_order == "positive":
            selected_patterns = sorted(
                candidate_patterns,
                key=lambda pat: (signed_float_by_pattern[pat], abs_float_by_pattern[pat]),
                reverse=True,
            )[:top_k]
        elif args.boundary_pattern_family_topn_order == "abs":
            selected_patterns = sorted(
                candidate_patterns,
                key=lambda pat: (abs_float_by_pattern[pat], abs(signed_float_by_pattern[pat]), runtime_proxy_by_pattern[pat]),
                reverse=True,
            )[:top_k]
        else:
            selected_patterns = sorted(
                candidate_patterns,
                key=lambda pat: (runtime_proxy_by_pattern[pat], abs_float_by_pattern[pat], pair_mass_by_pattern[pat]),
                reverse=True,
            )[:top_k]

        results: list[dict[str, object]] = []
        combined_signed = Fraction(0, 1)
        combined_abs = Fraction(0, 1)
        total_elapsed = 0.0
        for pattern in selected_patterns:
            result = evaluate_exact_boundary_pattern_family(
                X=X,
                target_pattern=pattern,
                family_scope=candidate_scope,
                pair_count_by_block=pair_count_by_block,
                total_pairs=total_pairs,
                mu=mu,
                phi=phi,
                spf=spf,
                even_window_card=even_window_card,
                progress=args.progress,
                progress_every=args.progress_every,
            )
            results.append(result)
            combined_signed += result["signed"]
            combined_abs += result["abs"]
            total_elapsed += float(result["elapsed_sec"])

        print("Active boundary exact top-N family batch report")
        print(f"  X                         = {X}")
        print(f"  support card              = {len(candidate_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  excluded patterns         = {sorted(excluded_patterns)}")
        print(f"  ranking order             = {args.boundary_pattern_family_topn_order}")
        print(f"  selected family count     = {len(results)}")
        print(f"  combined exact signed     = {float(combined_signed):.12e}")
        print(f"  combined exact abs        = {float(combined_abs):.12e}")
        print(f"  combined ratio            = {(abs(float(combined_signed)) / float(combined_abs)) if combined_abs else 0.0:.6f}")
        print(f"  combined elapsed sec      = {total_elapsed:.3f}")
        print(f"  Lean ℚ combined signed    = {fraction_to_q_literal(combined_signed)}")
        print()
        print("  pattern   G-count   pair mass     float signed est     float abs est        exact signed         exact abs            ratio     elapsed sec   avg ms/G")
        for result in results:
            pattern = result["pattern"]
            signed = result["signed"]
            abs_mass = result["abs"]
            elapsed_sec = float(result["elapsed_sec"])
            g_count = int(result["g_count"])
            ratio = (abs(float(signed)) / float(abs_mass)) if abs_mass else 0.0
            print(
                f"  {pattern[0]}:{pattern[1]:<5} {g_count:>8}  {int(result['pair_mass']):>10}  "
                f"{signed_float_by_pattern[pattern]:> .12e}  {abs_float_by_pattern[pattern]:> .12e}  "
                f"{float(signed):> .12e}  {float(abs_mass):> .12e}  {ratio:> .6f}  "
                f"{elapsed_sec:>11.3f}  {1000.0 * elapsed_sec / max(g_count, 1):>9.3f}"
            )
        return

    if args.boundary_pattern_product_exact_topn > 0:
        if args.true_series:
            raise SystemExit("--boundary-pattern-product-exact-topn is only implemented for the surrogate normalization")

        excluded_patterns = parse_selected_patterns(args.exclude_families)
        excluded_products = parse_selected_products(args.exclude_products)
        candidate_scope = active_support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in candidate_scope}
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            candidate_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        pair_mass_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        abs_coeff_proxy_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        runtime_proxy_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        divisor_count_cache: dict[int, int] = {}

        def divisor_count(q: int) -> int:
            if q not in divisor_count_cache:
                divisor_count_cache[q] = len(divisors_from_factorization(factorization(q, spf)))
            return divisor_count_cache[q]

        for block, pair_mass in pair_count_by_block.items():
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            block_count_by_pattern[pattern] += 1
            pair_mass_by_pattern[pattern] += pair_mass
            abs_coeff_proxy_by_pattern[pattern] += abs(coeff_scope[q] * coeff_scope[q2]) * pair_mass
            runtime_proxy_by_pattern[pattern] += divisor_count(q) * divisor_count(q2)

        top_k = max(args.boundary_pattern_product_exact_topn, 1)
        candidate_k = (
            max(args.boundary_family_candidate_patterns, top_k)
            if args.boundary_family_candidate_patterns > 0
            else max(top_k * 10, top_k)
        )
        candidate_patterns = sorted(
            block_count_by_pattern.keys(),
            key=lambda pat: (
                abs_coeff_proxy_by_pattern[pat],
                runtime_proxy_by_pattern[pat],
                pair_mass_by_pattern[pat],
                block_count_by_pattern[pat],
                -pat[0],
                -pat[1],
            ),
            reverse=True,
        )[:candidate_k]
        candidate_pattern_set = set(candidate_patterns)

        q_needed: set[int] = set()
        for block in pair_count_by_block:
            pattern, G = block
            if pattern in candidate_pattern_set:
                q_needed.add(G * pattern[0])
                q_needed.add(G * pattern[1])

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        abs_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for block in pair_count_by_block:
            pattern, G = block
            if pattern not in candidate_pattern_set:
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            signed_float_by_pattern[pattern] += val
            abs_float_by_pattern[pattern] += abs(val)
            processed += 1
            if args.progress and processed % max(1, min(args.progress_every, 1000)) == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-product-topn] processed_blocks={processed} "
                    f"candidate_patterns={len(candidate_pattern_set)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        patterns_by_product: dict[int, list[tuple[int, int]]] = defaultdict(list)
        block_count_by_product: dict[int, int] = defaultdict(int)
        pair_mass_by_product: dict[int, int] = defaultdict(int)
        runtime_proxy_by_product: dict[int, int] = defaultdict(int)
        signed_float_by_product: dict[int, float] = defaultdict(float)
        abs_float_by_product: dict[int, float] = defaultdict(float)

        for pattern in candidate_patterns:
            prod = pattern[0] * pattern[1]
            patterns_by_product[prod].append(pattern)
            block_count_by_product[prod] += block_count_by_pattern[pattern]
            pair_mass_by_product[prod] += pair_mass_by_pattern[pattern]
            runtime_proxy_by_product[prod] += runtime_proxy_by_pattern[pattern]
            signed_float_by_product[prod] += signed_float_by_pattern[pattern]
            abs_float_by_product[prod] += abs_float_by_pattern[pattern]

        products = list(patterns_by_product.keys())
        if args.boundary_pattern_product_topn_order == "negative":
            selected_products = sorted(products, key=lambda p: (signed_float_by_product[p], -abs_float_by_product[p]))[:top_k]
        elif args.boundary_pattern_product_topn_order == "positive":
            selected_products = sorted(products, key=lambda p: (signed_float_by_product[p], abs_float_by_product[p]), reverse=True)[:top_k]
        elif args.boundary_pattern_product_topn_order == "abs":
            selected_products = sorted(products, key=lambda p: (abs_float_by_product[p], abs(signed_float_by_product[p]), runtime_proxy_by_product[p]), reverse=True)[:top_k]
        else:
            selected_products = sorted(products, key=lambda p: (runtime_proxy_by_product[p], abs_float_by_product[p], pair_mass_by_product[p]), reverse=True)[:top_k]

        product_results: list[dict[str, object]] = []
        combined_signed = Fraction(0, 1)
        combined_abs = Fraction(0, 1)
        total_elapsed = 0.0
        for prod in selected_products:
            family_results: list[dict[str, object]] = []
            prod_signed = Fraction(0, 1)
            prod_abs = Fraction(0, 1)
            prod_elapsed = 0.0
            for pattern in sorted(patterns_by_product[prod]):
                result = evaluate_exact_boundary_pattern_family(
                    X=X,
                    target_pattern=pattern,
                    family_scope=candidate_scope,
                    pair_count_by_block=pair_count_by_block,
                    total_pairs=total_pairs,
                    mu=mu,
                    phi=phi,
                    spf=spf,
                    even_window_card=even_window_card,
                    progress=args.progress,
                    progress_every=args.progress_every,
                )
                family_results.append(result)
                prod_signed += result["signed"]
                prod_abs += result["abs"]
                prod_elapsed += float(result["elapsed_sec"])
            product_results.append({
                "product": prod,
                "patterns": sorted(patterns_by_product[prod]),
                "g_count": sum(int(r["g_count"]) for r in family_results),
                "pair_mass": sum(int(r["pair_mass"]) for r in family_results),
                "signed": prod_signed,
                "abs": prod_abs,
                "elapsed_sec": prod_elapsed,
            })
            combined_signed += prod_signed
            combined_abs += prod_abs
            total_elapsed += prod_elapsed

        print("Active boundary exact top-N product-class batch report")
        print(f"  X                         = {X}")
        print(f"  support card              = {len(candidate_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  excluded patterns         = {sorted(excluded_patterns)}")
        print(f"  excluded products         = {sorted(excluded_products)}")
        print(f"  ranking order             = {args.boundary_pattern_product_topn_order}")
        print(f"  selected product count    = {len(product_results)}")
        print(f"  combined exact signed     = {float(combined_signed):.12e}")
        print(f"  combined exact abs        = {float(combined_abs):.12e}")
        print(f"  combined ratio            = {(abs(float(combined_signed)) / float(combined_abs)) if combined_abs else 0.0:.6f}")
        print(f"  combined elapsed sec      = {total_elapsed:.3f}")
        print(f"  Lean ℚ combined signed    = {fraction_to_q_literal(combined_signed)}")
        print()
        print("  product  fams   G-count   pair mass     float signed est     float abs est        exact signed         exact abs            ratio     elapsed sec")
        for result in product_results:
            prod = int(result["product"])
            signed = result["signed"]
            abs_mass = result["abs"]
            elapsed_sec = float(result["elapsed_sec"])
            ratio = (abs(float(signed)) / float(abs_mass)) if abs_mass else 0.0
            print(
                f"  {prod:<7d} {len(result['patterns']):>4}  {int(result['g_count']):>8}  {int(result['pair_mass']):>10}  "
                f"{signed_float_by_product[prod]:> .12e}  {abs_float_by_product[prod]:> .12e}  "
                f"{float(signed):> .12e}  {float(abs_mass):> .12e}  {ratio:> .6f}  "
                f"{elapsed_sec:>11.3f}"
            )
            members = ' '.join(f"{a}:{b}" for (a, b) in result["patterns"])
            print(f"    members: {members}")
        return

    if args.boundary_pattern_product_exact_batch:
        if args.true_series:
            raise SystemExit("--boundary-pattern-product-exact-batch is only implemented for the surrogate normalization")

        excluded_patterns = parse_selected_patterns(args.exclude_families)
        excluded_products = parse_selected_products(args.exclude_products)
        target_products = sorted(set(args.boundary_pattern_product_exact_batch))
        candidate_scope = active_support
        coeff_scope = {q: normalized_sigma_trunc_summand_real_coeff(q, mu, phi) for q in candidate_scope}
        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            candidate_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        block_count_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        pair_mass_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        abs_coeff_proxy_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        runtime_proxy_by_pattern: dict[tuple[int, int], int] = defaultdict(int)
        divisor_count_cache: dict[int, int] = {}

        def divisor_count(q: int) -> int:
            if q not in divisor_count_cache:
                divisor_count_cache[q] = len(divisors_from_factorization(factorization(q, spf)))
            return divisor_count_cache[q]

        patterns_by_product: dict[int, list[tuple[int, int]]] = defaultdict(list)

        for block, pair_mass in pair_count_by_block.items():
            pattern, G = block
            if boundary_pattern_is_excluded(pattern, excluded_patterns, excluded_products):
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            block_count_by_pattern[pattern] += 1
            pair_mass_by_pattern[pattern] += pair_mass
            abs_coeff_proxy_by_pattern[pattern] += abs(coeff_scope[q] * coeff_scope[q2]) * pair_mass
            runtime_proxy_by_pattern[pattern] += divisor_count(q) * divisor_count(q2)

        for pattern in block_count_by_pattern:
            patterns_by_product[pattern[0] * pattern[1]].append(pattern)

        missing_products = [prod for prod in target_products if prod not in patterns_by_product]
        if missing_products:
            raise SystemExit(f"requested product classes not present after exclusions: {missing_products}")

        q_needed: set[int] = set()
        selected_patterns: set[tuple[int, int]] = set()
        for prod in target_products:
            for pattern in patterns_by_product[prod]:
                selected_patterns.add(pattern)
        for block in pair_count_by_block:
            pattern, G = block
            if pattern in selected_patterns:
                q_needed.add(G * pattern[0])
                q_needed.add(G * pattern[1])

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, sorted(q_needed),
            progress=args.progress,
        )

        signed_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        abs_float_by_pattern: dict[tuple[int, int], float] = defaultdict(float)
        processed = 0
        started = time.time()
        for block in pair_count_by_block:
            pattern, G = block
            if pattern not in selected_patterns:
                continue
            q = G * pattern[0]
            q2 = G * pattern[1]
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            signed_float_by_pattern[pattern] += val
            abs_float_by_pattern[pattern] += abs(val)
            processed += 1
            if args.progress and processed % max(1, min(args.progress_every, 1000)) == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-product-batch] processed_blocks={processed} "
                    f"selected_patterns={len(selected_patterns)} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        product_results: list[dict[str, object]] = []
        combined_signed = Fraction(0, 1)
        combined_abs = Fraction(0, 1)
        total_elapsed = 0.0
        for prod in target_products:
            family_results: list[dict[str, object]] = []
            prod_signed = Fraction(0, 1)
            prod_abs = Fraction(0, 1)
            prod_elapsed = 0.0
            for pattern in sorted(patterns_by_product[prod]):
                result = evaluate_exact_boundary_pattern_family(
                    X=X,
                    target_pattern=pattern,
                    family_scope=candidate_scope,
                    pair_count_by_block=pair_count_by_block,
                    total_pairs=total_pairs,
                    mu=mu,
                    phi=phi,
                    spf=spf,
                    even_window_card=even_window_card,
                    progress=args.progress,
                    progress_every=args.progress_every,
                )
                family_results.append(result)
                prod_signed += result["signed"]
                prod_abs += result["abs"]
                prod_elapsed += float(result["elapsed_sec"])
            product_results.append({
                "product": prod,
                "patterns": sorted(patterns_by_product[prod]),
                "g_count": sum(int(r["g_count"]) for r in family_results),
                "pair_mass": sum(int(r["pair_mass"]) for r in family_results),
                "signed": prod_signed,
                "abs": prod_abs,
                "elapsed_sec": prod_elapsed,
            })
            combined_signed += prod_signed
            combined_abs += prod_abs
            total_elapsed += prod_elapsed

        print("Active boundary exact explicit product-class batch report")
        print(f"  X                         = {X}")
        print(f"  support card              = {len(candidate_scope)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  excluded patterns         = {sorted(excluded_patterns)}")
        print(f"  excluded products         = {sorted(excluded_products)}")
        print(f"  selected products         = {target_products}")
        print(f"  combined exact signed     = {float(combined_signed):.12e}")
        print(f"  combined exact abs        = {float(combined_abs):.12e}")
        print(f"  combined ratio            = {(abs(float(combined_signed)) / float(combined_abs)) if combined_abs else 0.0:.6f}")
        print(f"  combined elapsed sec      = {total_elapsed:.3f}")
        print(f"  Lean ℚ combined signed    = {fraction_to_q_literal(combined_signed)}")
        print()
        print("  product  fams   G-count   pair mass     float signed est     float abs est        exact signed         exact abs            ratio     elapsed sec")
        for result in product_results:
            prod = int(result["product"])
            signed = result["signed"]
            abs_mass = result["abs"]
            elapsed_sec = float(result["elapsed_sec"])
            float_signed = sum(signed_float_by_pattern[pat] for pat in result["patterns"])
            float_abs = sum(abs_float_by_pattern[pat] for pat in result["patterns"])
            ratio = (abs(float(signed)) / float(abs_mass)) if abs_mass else 0.0
            print(
                f"  {prod:<7d} {len(result['patterns']):>4}  {int(result['g_count']):>8}  {int(result['pair_mass']):>10}  "
                f"{float_signed:> .12e}  {float_abs:> .12e}  "
                f"{float(signed):> .12e}  {float(abs_mass):> .12e}  {ratio:> .6f}  "
                f"{elapsed_sec:>11.3f}"
            )
            members = ' '.join(f"{a}:{b}" for (a, b) in result["patterns"])
            print(f"    members: {members}")
        return

    if args.boundary_signed_split_report:
        if args.true_series:
            raise SystemExit("--boundary-signed-split-report is only implemented for the surrogate normalization")

        selected_patterns: set[tuple[int, int]] = set()
        for raw in args.boundary_family_patterns:
            if ":" not in raw:
                raise SystemExit(f"invalid pattern {raw!r}; expected m:n")
            left, right = raw.split(":", 1)
            m = int(left)
            n = int(right)
            if m <= 0 or n <= 0:
                raise SystemExit(f"invalid pattern {raw!r}; entries must be positive")
            selected_patterns.add((m, n) if m <= n else (n, m))

        block_scope = active_support
        coeff_scope = {q: coeff_q[q] for q in block_scope}

        pair_count_by_block, total_pairs = build_active_boundary_block_table(
            block_scope,
            progress=args.progress,
            progress_every=args.progress_every,
        )

        ctx = build_surrogate_boundary_float_context(
            X, mu, phi, spf, even_window_card, block_scope,
            progress=args.progress,
        )

        signed_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        abs_by_block: dict[tuple[tuple[int, int], int], float] = defaultdict(float)
        all_blocks = list(pair_count_by_block.keys())
        block_range = None
        if args.block_range is not None:
            start, end = args.block_range
            if start < 0 or end < start:
                raise SystemExit("--block-range must satisfy 0 <= START <= END")
            start = min(start, len(all_blocks))
            end = min(end, len(all_blocks))
            block_range = (start, end)
            all_blocks = all_blocks[start:end]
        block_progress_every = min(max(args.progress_every, 1), 50_000)
        processed = 0
        started = time.time()
        for pattern, G in all_blocks:
            m, n = pattern
            q = G * m
            q2 = G * n
            processed += 1
            # `(pattern,G)` is an unordered reversible block, so evaluate one orientation
            # and double it instead of rescanning both ordered pairs.
            val = 2.0 * surrogate_boundary_pair_contribution_float_cached(X, q, q2, ctx)
            block = (pattern, G)
            signed_by_block[block] = val
            abs_by_block[block] = abs(val)
            if args.progress and processed % block_progress_every == 0:
                elapsed = time.time() - started
                print(
                    f"[boundary-signed-split:pass2] processed_blocks={processed}/{len(all_blocks)} "
                    f"elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        if block_range is not None:
            records = []
            for block in all_blocks:
                pattern, G = block
                records.append({
                    "pattern": [pattern[0], pattern[1]],
                    "G": G,
                    "pair_count": pair_count_by_block[block],
                    "signed": signed_by_block[block],
                    "abs": abs_by_block[block],
                })
            payload = {
                "mode": "boundary-signed-split-chunk",
                "X": X,
                "active_support_card": len(active_support),
                "active_ordered_pairs": total_pairs,
                "total_active_blocks": len(pair_count_by_block),
                "block_range": [block_range[0], block_range[1]],
                "top_remove": max(args.boundary_pattern_g_remove_top, 0),
                "selected_patterns": [list(p) for p in sorted(selected_patterns)],
                "records": records,
            }
            if args.checkpoint_json:
                with open(args.checkpoint_json, "w", encoding="utf-8") as fh:
                    json.dump(payload, fh, indent=2, sort_keys=True)
            print("Boundary signed split chunk report")
            print(f"  X                        = {X}")
            print(f"  block range              = [{block_range[0]}, {block_range[1]})")
            print(f"  total active blocks      = {len(pair_count_by_block)}")
            print(f"  evaluated chunk blocks   = {len(all_blocks)}")
            print(f"  chunk signed total       = {math.fsum(signed_by_block.values()):.12e}")
            print(f"  chunk abs total          = {math.fsum(abs_by_block.values()):.12e}")
            if args.checkpoint_json:
                print(f"  wrote checkpoint json    = {args.checkpoint_json}")
            return

        ranked_blocks = sorted(
            signed_by_block.keys(),
            key=lambda block: (
                abs_by_block[block],
                abs(signed_by_block[block]),
                pair_count_by_block[block],
                -block[1],
                -block[0][0],
                -block[0][1],
            ),
            reverse=True,
        )
        top_remove = max(args.boundary_pattern_g_remove_top, 0)
        top_global_blocks = set(ranked_blocks[:top_remove])
        expanded_family_blocks = {
            block for block in ranked_blocks[top_remove:]
            if block[0] in selected_patterns
        }
        selected_blocks = top_global_blocks | expanded_family_blocks
        coherent_threshold = 1.0 - 1e-12
        coherent_leftover_blocks = [
            block for block in ranked_blocks
            if block not in selected_blocks
            and pair_count_by_block[block] == 2
            and ((abs(signed_by_block[block]) / abs_by_block[block]) if abs_by_block[block] else 0.0) >= coherent_threshold
        ]
        incoherent_leftover_blocks = [
            block for block in ranked_blocks
            if block not in selected_blocks and block not in coherent_leftover_blocks
        ]

        selected_signed = math.fsum(signed_by_block[block] for block in selected_blocks)
        selected_abs = math.fsum(abs_by_block[block] for block in selected_blocks)
        coh2_signed = math.fsum(signed_by_block[block] for block in coherent_leftover_blocks)
        coh2_abs = math.fsum(abs_by_block[block] for block in coherent_leftover_blocks)
        incoh_signed = math.fsum(signed_by_block[block] for block in incoherent_leftover_blocks)
        incoh_abs = math.fsum(abs_by_block[block] for block in incoherent_leftover_blocks)
        active_boundary_signed = selected_signed + coh2_signed + incoh_signed
        inactive_correction = boundary_total - active_boundary_signed

        print("Surrogate boundary signed split report")
        print("  NOTE                      = selected/coh2/incoh is computed on full active scope; the correction below is the contribution outside active scope to the full surrogate boundary")
        print(f"  X                         = {X}")
        print(f"  active support card       = {len(active_support)}")
        print(f"  active ordered pairs      = {total_pairs}")
        print(f"  distinct active blocks    = {len(ranked_blocks)}")
        print(f"  top global blocks selected = {len(top_global_blocks)}")
        print(f"  expanded family patterns   = {sorted(selected_patterns)}")
        print(f"  expanded family blocks     = {len(expanded_family_blocks)}")
        print()
        print("  active-scope signed split")
        print(f"    selected_signed         = {selected_signed:.12e}")
        print(f"    selected_abs            = {selected_abs:.12e}")
        print(f"    coh2_signed             = {coh2_signed:.12e}")
        print(f"    coh2_abs                = {coh2_abs:.12e}")
        print(f"    incoh_signed            = {incoh_signed:.12e}")
        print(f"    incoh_abs               = {incoh_abs:.12e}")
        print(f"    active_boundary_signed  = {active_boundary_signed:.12e}")
        print(f"    abs(active_boundary)    = {abs(active_boundary_signed):.12e}")
        print()
        print("  full-boundary reconciliation")
        print(f"    full_boundary_signed    = {boundary_total:.12e}")
        print(f"    abs(full_boundary)      = {abs(boundary_total):.12e}")
        print(f"    inactive_correction     = {inactive_correction:.12e}")
        print(f"    abs(inactive_correction)= {abs(inactive_correction):.12e}")
        print(f"    target_26               = {26.0:.12e}")
        return

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

    print_normalization_header()
    print(f"active periodic-main support cutoff = {q_active_max}")
    print(f"active periodic-main support card = {len(active_support)}")
    print(f"active periodic-main unordered offdiag pairs = {active_main_unordered_pairs}")
    print()
    print(f"diagonalExact              = {rescale(diagonal):.12f}")
    print(f"windowEnergyExact          = {rescale(total_window_energy):.12f}")
    print(f"pairCorrelationTotal       = {rescale(pair_correlation_total):.12f}")
    print(f"periodicMainTotal          = {rescale(periodic_main_total):.12f}")
    print(f"  periodicMainCoprime      = {rescale(periodic_main_coprime):.12f}")
    print(f"  periodicMainNonCoprime   = {rescale(periodic_main_noncoprime):.12f}")
    print(f"boundaryTotal              = {rescale(boundary_total):.12f}")
    if pair_correlation_total != 0.0:
        print(f"boundaryShareOfPairCorr    = {boundary_total / pair_correlation_total:.12f}")
    if total_window_energy != 0.0:
        print(f"diagonalShareOfEnergy      = {diagonal / total_window_energy:.12f}")
        print(f"offdiagShareOfEnergy       = {pair_correlation_total / total_window_energy:.12f}")

    if args.emit_pointwise_certificate:
        print()
        if args.true_series:
            print("Pointwise direct Route A true-series numerical audit")
            print("  WARNING                   = uses numerical Euler-product approximation for ramanujanSeriesOnWindow.C.C2, not a theorem-safe certificate")
        else:
            print("Pointwise direct Route A surrogate certificate data")
            print("  WARNING                   = uses C2_numeric = 1/10 surrogate, not ramanujanSeriesOnWindow.C.C2")
        print(f"  X                         = {X}")
        print(f"  X0                        = 1000000")
        print("  audited inequalities:")
        print(f"    D_main(X)               = {rescale(diag_main):.12f}")
        print(f"    D_smallRest(X)          = {rescale(diag_small_rest):.12f}")
        print(f"    D_tail(X)               = {rescale(diag_tail):.12f}")
        print(f"    |periodicMain(X)|       = {abs(rescale(periodic_main_total)):.12f}")
        print(f"    |boundary(X)|           = {abs(rescale(boundary_total)):.12f}")
        print(f"    windowEnergy(X)         = {rescale(total_window_energy):.12f}")
        print("  diagonal main six terms:")
        for q in [3, 5, 6, 7, 10, 14]:
            print(f"    q={q:<2d}  E_q = {rescale(diag_energy_q[q]):.12f}")
        print("  diagonal small-rest support (q <= 50, outside main, nonzero energy):")
        print(f"    {diag_small_rest_support}")

    if args.emit_lean_checkle:
        print()
        print("Lean CheckLE payload (surrogate audit values only)")
        if args.true_series:
            print("  WARNING = not emitted because this mode is intended for surrogate payloads only")
        else:
            checks = [
                ("surrogate_boundary_abs_x0", abs(boundary_total), 26),
                ("surrogate_periodic_main_abs_x0", abs(periodic_main_total), 37603),
                ("surrogate_diag_main_x0", diag_main, 36326),
                ("surrogate_diag_smallRest_x0", diag_small_rest, 1207),
                ("surrogate_diag_tail_x0", diag_tail, 100),
            ]
            print("open Goldbach.Cert.MajorArcCertChecker")
            print()
            print("def q0MinorPointwiseSurrogateChecks : List CheckLE :=")
            print("  [")
            for name, lhs, rhs in checks:
                print("    {")
                print(f"      name := \"{name}\"")
                print(f"      lhs := {decimal_to_q_literal(lhs)}")
                print(f"      rhs := ({rhs} : ℚ)")
                print("    },")
            print("  ]")
            print()
            print("def q0MinorPointwiseSurrogateCert : Cert :=")
            print("  { checks := q0MinorPointwiseSurrogateChecks }")
            print()
            print("theorem q0MinorPointwiseSurrogateCert_valid : q0MinorPointwiseSurrogateCert.Valid := by")
            print("  native_decide")
            print()
            print("-- diagonal small-rest support (q <= 50, outside main, nonzero energy)")
            print(f"-- {diag_small_rest_support}")

    if args.diag_breakdown:
        diag_main = math.fsum(eq for q, eq in diag_energy_q.items() if q in DIAG_MAIN_LOW_Q)
        diag_small_rest = math.fsum(
            eq for q, eq in diag_energy_q.items() if q not in DIAG_MAIN_LOW_Q and q <= 50
        )
        diag_tail = math.fsum(
            eq for q, eq in diag_energy_q.items() if q not in DIAG_MAIN_LOW_Q and q > 50
        )

        print()
        print("Diagonal per-q breakdown")
        print(f"  total diagonal = {diagonal:.12f}")
        print(f"  support size = {len(support)}")
        print(f"  off-support q count = {Q0 - len(support)} (exactly zero by coefficient support)")
        print()
        print("Diagonal main/small-rest/tail split")
        print("  piece        mass                 share")
        for label, mass in [
            ("main", diag_main),
            ("smallRest", diag_small_rest),
            ("tail", diag_tail),
        ]:
            share = (mass / diagonal) if diagonal else 0.0
            print(f"  {label:<10} {mass:> .12e}  {share:> .6f}")

        top = min(args.diag_top, len(support))
        top_qs = sorted(diag_energy_q.items(), key=lambda kv: kv[1], reverse=True)[:top]
        print()
        print(f"Top {top} q by diagonal energy")
        print("  q      support  coeff               E_q                 share        cumulative")
        cumulative = 0.0
        for q, eq in top_qs:
            cumulative += eq
            share = (eq / diagonal) if diagonal else 0.0
            cshare = (cumulative / diagonal) if diagonal else 0.0
            print(
                f"  {q:>5}  yes      {coeff_q[q]:> .12e}  {eq:> .12e}  {share:> .6f}    {cshare:> .6f}"
            )

        print()
        print("Mass by increasing q range")
        ranges = [
            (1, 10),
            (11, 50),
            (51, 100),
            (101, 500),
            (501, 1000),
            (1001, 5000),
            (5001, Q0),
        ]
        print("  range           signed/abs mass      share")
        for lo, hi in ranges:
            mass = math.fsum(eq for q, eq in diag_energy_q.items() if lo <= q <= hi)
            share = (mass / diagonal) if diagonal else 0.0
            print(f"  [{lo:>4},{hi:>5}]   {mass:> .12e}  {share:> .6f}")

        omega_mass: dict[int, float] = defaultdict(float)
        spf_mass: dict[int, float] = defaultdict(float)
        increasing_cumulative = 0.0
        print()
        print("First support q by increasing q")
        print("  q      coeff               E_q                 cumulative")
        for q in sorted(support)[:top]:
            increasing_cumulative += diag_energy_q[q]
            cshare = (increasing_cumulative / diagonal) if diagonal else 0.0
            print(
                f"  {q:>5}  {coeff_q[q]:> .12e}  {diag_energy_q[q]:> .12e}  {cshare:> .6f}"
            )

        for q, eq in diag_energy_q.items():
            fac = factorization(q, spf)
            omega_mass[len(fac)] += eq
            if fac:
                spf_mass[min(fac)] += eq
            else:
                spf_mass[1] += eq

        print()
        print("Mass by omega(q)")
        print("  omega   mass                 share")
        for omega in sorted(omega_mass):
            mass = omega_mass[omega]
            share = (mass / diagonal) if diagonal else 0.0
            print(f"  {omega:>5}   {mass:> .12e}  {share:> .6f}")

        print()
        print("Mass by smallest prime factor")
        print("  spf     mass                 share")
        for p, mass in sorted(spf_mass.items(), key=lambda kv: (-kv[1], kv[0])):
            share = (mass / diagonal) if diagonal else 0.0
            print(f"  {p:>5}   {mass:> .12e}  {share:> .6f}")


if __name__ == "__main__":
    main()
