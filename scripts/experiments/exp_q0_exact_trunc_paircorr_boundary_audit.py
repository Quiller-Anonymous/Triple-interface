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
import heapq
import json
import math
import sys
import time
from collections import Counter, defaultdict
from decimal import Decimal
from fractions import Fraction


H = 10_000
Q0 = 30_000
C2_NUMERIC = 0.1
DIAG_MAIN_LOW_Q = {3, 5, 6, 7, 10, 14}


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
    ap.add_argument("--diag-tail-one-subchunk-part-size", type=int, default=0,
                    help="If positive, split the selected one-subchunk payload into smaller explicit part supports of this size.")
    ap.add_argument("--emit-periodic-main-rat-total", action="store_true",
                    help="Emit the exact surrogate periodic-main rational total at the current X as a Lean ℚ literal.")
    ap.add_argument("--emit-boundary-pair-rat", nargs=2, type=int, metavar=("Q", "Q2"),
                    help="Emit the exact surrogate boundary pair contribution for one ordered pair as a Lean ℚ literal.")
    ap.add_argument("--emit-boundary-rat-total", action="store_true",
                    help="Emit the exact surrogate boundary rational total and nonzero ordered-pair count.")
    ap.add_argument("--emit-boundary-rat-terms", action="store_true",
                    help="Emit the finite nonzero ordered-pair rational term list for the surrogate boundary certificate.")
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
    ap.add_argument("--boundary-signed-split-report", action="store_true",
                    help="Compute the full active-scope signed selected/coh2/incoh split and compare it against the full surrogate boundary via an inactive correction term.")
    ap.add_argument("--boundary-signed-split-fast", action="store_true",
                    help="Fast path for active-scope signed split evaluation and chunk export. Skips unrelated full boundary pipeline work.")
    ap.add_argument("--block-range", nargs=2, type=int, metavar=("START", "END"),
                    help="Evaluate only active reversible blocks in the half-open index range [START, END). Intended for chunked boundary-signed-split runs.")
    ap.add_argument("--combine-boundary-chunks", nargs="*", default=[],
                    help="Combine chunk JSON files emitted by --boundary-signed-split-fast or --boundary-signed-split-report --block-range.")
    ap.add_argument("--emit-boundary-final-certificate", action="store_true",
                    help="With --combine-boundary-chunks, emit Lean-facing ℚ certificate defs for active signed total, inactive correction, and full boundary.")
    ap.add_argument("--boundary-full-signed-decimal", type=str, default="",
                    help="With --emit-boundary-final-certificate, the full surrogate boundary signed decimal to package as the final full certificate value.")
    args = ap.parse_args()

    if args.combine_boundary_chunks:
        top_remove_ref = None
        selected_patterns_ref = None
        total_active_blocks_ref = None
        X_ref = None
        covered_ranges: list[tuple[int, int]] = []
        chunk_paths = list(args.combine_boundary_chunks)

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
        support_ordered_pairs = len(support) * max(len(support) - 1, 0)
        candidate_pairs: list[tuple[int, int]] = []
        q_needed: set[int] = set()
        scanned = 0
        started_scan = time.time()
        pair_limit = args.pair_limit if args.pair_limit > 0 else 0
        for q in support:
            for q2 in support:
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
        fac_q = factorization(q, spf)
        divs_q = divisors_from_factorization(fac_q)
        coeff_q = surrogate_coeff_rat(q, mu, phi)
        energy_q = centered_ramanujan_window_energy_rat(
            X, q, mu, phi, even_window, even_window_card
        )
        term_q = surrogate_diagonal_energy_q_rat(
            X, q, mu, phi, even_window, even_window_card
        )
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
            avg_g = ramanujan_gcd_class_window_average_rat(X, q, g, even_window_card)
            count_g = avg_g * even_window_card
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
        subchunk_count = math.ceil(len(chunk_support) / subchunk_size)
        subchunk_index = args.diag_tail_subchunk_index
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
        print("Surrogate diagonal tail exact rational subchunks")
        print(f"  X                         = {X}")
        print(f"  tail support card         = {len(tail_support)}")
        print(f"  chunk size                = {chunk_size}")
        print(f"  subchunk size             = {subchunk_size}")
        print(f"  chunk index               = {chunk_index}")
        print(f"  chunk support indices     = [{start_idx}, {chunk_end_idx})")
        print(f"  chunk q range             = [{chunk_support[0]}, {chunk_support[-1]}]")
        print(f"  chunk rational numerator  = {chunk_total.numerator}")
        print(f"  chunk rational denominator= {chunk_total.denominator}")
        print(f"  chunk Lean ℚ literal      = {fraction_to_q_literal(chunk_total)}")
        print(f"  chunk float value         = {float(chunk_total):.15f}")
        print("  Subchunk table")
        for subchunk_index, abs_start, abs_end, first_q, last_q, sub_total in subchunk_payloads:
            print(
                f"    subchunk {subchunk_index:03d}: idx=[{abs_start},{abs_end}) "
                f"q=[{first_q},{last_q}] value={fraction_to_q_literal(sub_total)}"
            )
        print("  Lean payload")
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
        print()
        print(f"theorem {cert_name}_eq_subchunk_sum :")
        print(f"    {subchunk_sum_expr} = {cert_name} := by")
        print(f"  norm_num [{cert_name},")
        for i, name in enumerate(subchunk_names):
            comma = "," if i + 1 < len(subchunk_names) else ""
            print(f"    {name}{comma}")
        print("  ]")
        print()
        print("  Lean goal stubs for the remaining exact equalities")
        for subchunk_index, abs_start, abs_end, first_q, last_q, _sub_total in subchunk_payloads:
            sub_name = subchunk_names[subchunk_index]
            sub_support_name = subchunk_support_names[subchunk_index]
            theorem_stub_name = f"surrogateDiagonalTailChunk{chunk_label}Sub{subchunk_index:03d}_eq_cert"
            print(f"-- theorem {theorem_stub_name} :")
            print(f"--     (∑ q ∈ {sub_support_name},")
            print("--         surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
            print(f"--       = {sub_name} := by")
            print(
                f"--   -- subchunk {subchunk_index:03d} covers tail-support indices [{abs_start},{abs_end}) "
                f"and q from {first_q} to {last_q}"
            )
            print("--   -- generated certificate proof")
        print()
        print(f"theorem surrogateDiagonalTailChunk{chunk_label}_eq_cert_of_subchunked_sum")
        print("    (hsubchunked :")
        print(f"      (∑ q ∈ {support_name},")
        print("          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)")
        print(f"        = {subchunk_sum_expr}) :")
        print(f"    {theorem_name} := by")
        print(f"  apply {wrapper_name}")
        print(f"  rw [hsubchunked, {cert_name}_eq_subchunk_sum]")
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
