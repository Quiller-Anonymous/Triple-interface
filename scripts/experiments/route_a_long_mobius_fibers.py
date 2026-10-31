#!/usr/bin/env python3
"""Fixed-center long-Mobius fiber diagnostic.

Examples:
    python3 scripts/experiments/route_a_long_mobius_fibers.py 7077888 16777216
    python3 scripts/experiments/route_a_long_mobius_fibers.py 16777216 --square-cutoff 7
    python3 scripts/experiments/route_a_long_mobius_fibers.py 16777216 \
      --square-cutoff 7 --auxiliary-upper 97

Default mode uses z = ceil(log(N)^20), capped only where the cap does not
change b_z on the tested integer range. ``--square-cutoff`` selects a
SURROGATE finite-scale experiment. No output is an asymptotic theorem or a
Goldbach certificate.
"""

from __future__ import annotations

import argparse
import json
import math
from array import array


def icbrt(n: int) -> int:
    """Return the exact floor cube root of a nonnegative integer."""
    if n < 0:
        raise ValueError("icbrt requires n >= 0")
    lo, hi = 0, 1 << ((n.bit_length() + 2) // 3)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid <= n:
            lo = mid
        else:
            hi = mid
    return lo


def ceildiv(a: int, b: int) -> int:
    if b <= 0:
        raise ValueError("positive divisor required")
    return -((-a) // b)


def arithmetic_tables(limit: int):
    """Build Mobius and Liouville tables with a linear sieve."""
    spf = array("I", [0]) * (limit + 1)
    mu = array("b", [0]) * (limit + 1)
    liouville = array("b", [0]) * (limit + 1)
    primes: list[int] = []
    if limit >= 1:
        mu[1] = liouville[1] = 1

    for n in range(2, limit + 1):
        if spf[n] == 0:
            spf[n] = n
            primes.append(n)
            mu[n] = liouville[n] = -1

        for p in primes:
            value = n * p
            if value > limit:
                break
            spf[value] = p
            liouville[value] = -liouville[n]
            if n % p == 0:
                mu[value] = 0
                break
            mu[value] = -mu[n]

    return spf, mu, liouville, primes


def localized_liouville(limit, cutoff, mu, liouville, primes):
    """Return b_z(n) = lambda(n) with small-prime square factors removed."""
    if cutoff >= math.isqrt(limit):
        return mu

    excluded = bytearray(limit + 1)
    for p in primes:
        if p > cutoff or p * p > limit:
            break
        for n in range(p * p, limit + 1, p * p):
            excluded[n] = 1

    result = array("b", [0]) * (limit + 1)
    for n in range(1, limit + 1):
        if not excluded[n]:
            result[n] = liouville[n]
    return result


def distinct_prime_factors_in_range(n, spf, lower, upper):
    """Return the distinct prime factors p of n with lower < p <= upper."""
    factors = []
    while n > 1:
        prime = spf[n]
        if lower < prime <= upper:
            factors.append(prime)
        while n % prime == 0:
            n //= prime
    return tuple(factors)


def bump(x: float) -> float:
    """Smooth bump supported in (0.66, 0.74), within (1/2, 3/4)."""
    value = (x - 0.70) / 0.04
    if abs(value) >= 1.0:
        return 0.0
    return math.exp(1.0 - 1.0 / (1.0 - value * value))


def quantiles(values):
    if not values:
        return None
    ordered = sorted(values)
    count = len(ordered)
    return {
        str(p): ordered[min(count - 1, int(p * (count - 1)))]
        for p in (0.0, 0.1, 0.5, 0.9, 1.0)
    }


def empty_stratum():
    return {
        "fibers": 0,
        "S0": 0,
        "T": 0.0,
        "V": 0.0,
        "Vw": 0.0,
        "W2": 0.0,
    }


def update_stratum(stats, length, correlation, weight):
    stats["fibers"] += 1
    stats["S0"] += length
    stats["T"] += weight * correlation
    stats["V"] += (correlation * correlation) / length
    stats["Vw"] += weight * weight * (correlation * correlation) / length
    stats["W2"] += weight * weight * length


def finish_stratum(stats, center):
    return {
        "fibers": stats["fibers"],
        "S0": stats["S0"],
        "T_over_N": stats["T"] / center,
        "V": stats["V"],
        "Vw": stats["Vw"],
        "W2": stats["W2"],
        "unweighted_CS_bound_over_N": (
            math.sqrt(stats["W2"] * stats["V"]) / center
        ),
        "weight_adapted_CS_bound_over_N": (
            math.sqrt(stats["S0"] * stats["Vw"]) / center
        ),
    }


def audit(
    center: int,
    cutoff: int | None,
    max_long: int,
    auxiliary_upper: int | None,
):
    if center <= 0 or center % 2:
        raise ValueError("N must be a positive even integer")

    # Exact integer endpoints for D=N^(2/3) and Y=N^(1/3).
    long_lower = icbrt((center * center) // 8) + 1
    long_upper = icbrt((27 * center * center) // 64)
    short_lower = icbrt(center // 8) + 1
    short_upper = icbrt((27 * center) // 64)

    if long_upper > max_long:
        raise ValueError(
            f"long-variable endpoint {long_upper} exceeds --max-long={max_long}"
        )

    log_center = math.log(center)
    short_scale = center ** (1.0 / 3.0)  # Used only in the smooth weight.
    spf, mu, liouville, primes = arithmetic_tables(long_upper)

    if cutoff is None:
        # A cap at long_upper changes no square-divisibility test in this range.
        square_cutoff = min(long_upper, math.ceil(log_center**20))
        mode = "prescribed-cutoff coefficient diagnostic"
    else:
        if cutoff < 1:
            raise ValueError("--square-cutoff must be >= 1")
        square_cutoff = cutoff
        mode = "SURROGATE cutoff diagnostic"

    coefficient = localized_liouville(
        long_upper, square_cutoff, mu, liouville, primes
    )
    if auxiliary_upper is not None and auxiliary_upper < 2:
        raise ValueError("--auxiliary-upper must be >= 2")
    auxiliary_upper_used = (
        min(auxiliary_upper, long_upper)
        if auxiliary_upper is not None
        else None
    )
    auxiliary_pool_empty = (
        auxiliary_upper_used is not None
        and auxiliary_upper_used <= square_cutoff
    )
    auxiliary_factor_cache = {}

    def auxiliary_factors(n):
        cached = auxiliary_factor_cache.get(n)
        if cached is None:
            cached = distinct_prime_factors_in_range(
                n,
                spf,
                square_cutoff,
                auxiliary_upper_used,
            )
            auxiliary_factor_cache[n] = cached
        return cached

    short_weight = {
        m: bump(m / short_scale) * math.log(m)
        for m in range(short_lower, short_upper + 1)
    }

    lengths = []
    correlations = []
    t_terms = []
    variance_terms = []
    weight_energy_terms = []
    diagonal_terms = []
    common_absolute_terms = []
    auxiliary_stats = {
        "low_union_T": 0.0,
        "low_union_absolute": 0.0,
        "low_union_V": 0.0,
        "low_union_Vw": 0.0,
        "both_zero_T": 0.0,
        "both_zero_absolute": 0.0,
        "both_zero_V": 0.0,
        "both_zero_Vw": 0.0,
    }
    strata = {
        "active_all": empty_stratum(),
        "active_m_eq_b": empty_stratum(),
        "active_m_ne_b": empty_stratum(),
        "active_g_eq_1": empty_stratum(),
        "active_g_gt_1": empty_stratum(),
        "active_coprime_rs_A": empty_stratum(),
        "active_noncoprime_rs_A": empty_stratum(),
    }

    solution_mass = 0
    for m in range(short_lower, short_upper + 1):
        for b in range(short_lower, short_upper + 1):
            gcd = math.gcd(m, b)
            if center % gcd:
                continue

            r, s, reduced_center = m // gcd, b // gcd, center // gcd
            d0 = 0 if s == 1 else (reduced_center * pow(r, -1, s)) % s
            a0 = (reduced_center - r * d0) // s

            t_min = max(
                ceildiv(long_lower - d0, s),
                ceildiv(a0 - long_upper, r),
            )
            t_max = min(
                (long_upper - d0) // s,
                (a0 - long_lower) // r,
            )
            length = t_max - t_min + 1
            if length <= 0:
                continue

            correlation = 0
            diagonal = 0
            low_union_correlation = 0
            low_union_absolute = 0
            both_zero_correlation = 0
            both_zero_absolute = 0
            excluded_auxiliary_product = r * s * reduced_center
            for t in range(t_min, t_max + 1):
                d = d0 + s * t
                a = a0 - r * t
                assert long_lower <= d <= long_upper
                assert long_lower <= a <= long_upper
                assert m * d + b * a == center

                value = int(coefficient[d]) * int(coefficient[a])
                correlation += value
                diagonal += value * value

                if auxiliary_upper_used is not None:
                    d_has_usable = any(
                        excluded_auxiliary_product % p
                        for p in auxiliary_factors(d)
                    )
                    a_has_usable = any(
                        excluded_auxiliary_product % p
                        for p in auxiliary_factors(a)
                    )
                    if not d_has_usable or not a_has_usable:
                        low_union_correlation += value
                        low_union_absolute += abs(value)
                    if not d_has_usable and not a_has_usable:
                        both_zero_correlation += value
                        both_zero_absolute += abs(value)

            weight = short_weight[m] * short_weight[b]
            solution_mass += length
            lengths.append(length)
            correlations.append(correlation / length)
            t_terms.append(weight * correlation)
            variance_terms.append((correlation * correlation) / length)
            weight_energy_terms.append(weight * weight * length)
            diagonal_terms.append(diagonal / length)

            if weight != 0.0:
                update_stratum(
                    strata["active_all"], length, correlation, weight
                )
                update_stratum(
                    strata["active_m_eq_b" if m == b else "active_m_ne_b"],
                    length,
                    correlation,
                    weight,
                )

                if auxiliary_upper_used is not None:
                    auxiliary_stats["low_union_T"] += (
                        weight * low_union_correlation
                    )
                    auxiliary_stats["low_union_absolute"] += (
                        abs(weight) * low_union_absolute
                    )
                    auxiliary_stats["low_union_V"] += (
                        low_union_correlation * low_union_correlation / length
                    )
                    auxiliary_stats["low_union_Vw"] += (
                        weight
                        * weight
                        * low_union_correlation
                        * low_union_correlation
                        / length
                    )
                    auxiliary_stats["both_zero_T"] += (
                        weight * both_zero_correlation
                    )
                    auxiliary_stats["both_zero_absolute"] += (
                        abs(weight) * both_zero_absolute
                    )
                    auxiliary_stats["both_zero_V"] += (
                        both_zero_correlation * both_zero_correlation / length
                    )
                    auxiliary_stats["both_zero_Vw"] += (
                        weight
                        * weight
                        * both_zero_correlation
                        * both_zero_correlation
                        / length
                    )
                update_stratum(
                    strata["active_g_eq_1" if gcd == 1 else "active_g_gt_1"],
                    length,
                    correlation,
                    weight,
                )
                update_stratum(
                    strata[
                        "active_coprime_rs_A"
                        if math.gcd(r * s, reduced_center) == 1
                        else "active_noncoprime_rs_A"
                    ],
                    length,
                    correlation,
                    weight,
                )

            if math.gcd(r * s, reduced_center) > 1:
                common_absolute_terms.append(abs(weight) * length)

    selected_sum = math.fsum(t_terms)
    variance = math.fsum(variance_terms)
    weight_energy = math.fsum(weight_energy_terms)
    diagonal = math.fsum(diagonal_terms)
    cs_bound = math.sqrt(weight_energy * variance)

    return {
        "N": center,
        "mode": mode,
        "cutoff_used": square_cutoff,
        "long_interval": [long_lower, long_upper],
        "short_interval": [short_lower, short_upper],
        "bump": "exp(1-1/(1-((x-0.70)/0.04)^2)) on |...|<1",
        "nonempty_fibers": len(lengths),
        "S0": solution_mass,
        "W2": weight_energy,
        "T_over_N": selected_sum / center,
        "V": variance,
        "V_over_S0": variance / solution_mass if solution_mass else None,
        "CS_bound_over_N": cs_bound / center,
        "abs_T_over_CS_bound": (
            abs(selected_sum) / cs_bound if cs_bound else None
        ),
        "diagonal_benchmark": diagonal,
        "M_quantiles": quantiles(lengths),
        "C_over_M_quantiles": quantiles(correlations),
        "common_factor_absolute_envelope_over_N": (
            math.fsum(common_absolute_terms) / center
        ),
        "available_primes_above_cutoff_up_to_long_endpoint": sum(
            p > square_cutoff for p in primes
        ),
        "marked_operator_norms": "NOT COMPUTED: signed matrix unspecified",
        "auxiliary_pool_diagnostic": (
            None
            if auxiliary_upper_used is None
            else {
                "pool": (
                    "empty because auxiliary_upper <= square_cutoff"
                    if auxiliary_pool_empty
                    else (
                        f"primes {square_cutoff} < p <= {auxiliary_upper_used} "
                        "with p not dividing r*s*A"
                    )
                ),
                "pool_empty_by_cutoff": auxiliary_pool_empty,
                "warning": (
                    "SURROGATE finite-scale diagnostic unless the requested "
                    "cutoffs equal the asymptotic application"
                ),
                "low_union_signed_T_over_N": (
                    auxiliary_stats["low_union_T"] / center
                ),
                "low_union_absolute_envelope_over_N": (
                    auxiliary_stats["low_union_absolute"] / center
                ),
                "low_union_V": auxiliary_stats["low_union_V"],
                "low_union_Vw": auxiliary_stats["low_union_Vw"],
                "both_zero_signed_T_over_N": (
                    auxiliary_stats["both_zero_T"] / center
                ),
                "both_zero_absolute_envelope_over_N": (
                    auxiliary_stats["both_zero_absolute"] / center
                ),
                "both_zero_V": auxiliary_stats["both_zero_V"],
                "both_zero_Vw": auxiliary_stats["both_zero_Vw"],
            }
        ),
        "active_strata": {
            name: finish_stratum(stats, center)
            for name, stats in strata.items()
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("centers", nargs="+", type=int)
    parser.add_argument("--square-cutoff", type=int, default=None)
    parser.add_argument(
        "--auxiliary-upper",
        type=int,
        default=None,
        help=(
            "Report the signed low-factor remainder for auxiliary primes "
            "square_cutoff < p <= this value; this is normally surrogate-only"
        ),
    )
    parser.add_argument("--max-long", type=int, default=2_000_000)
    args = parser.parse_args()

    for center in args.centers:
        print(
            json.dumps(
                audit(
                    center,
                    args.square_cutoff,
                    args.max_long,
                    args.auxiliary_upper,
                ),
                sort_keys=True,
            )
        )


if __name__ == "__main__":
    main()
