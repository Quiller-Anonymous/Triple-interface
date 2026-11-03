#!/usr/bin/env python3
"""Diagnostic ledger for the balanced BMOR Route A adapter.

This script does not certify a theorem. It evaluates the explicit bounds already exposed in Lean
and compares finite denominator cutoffs before further formalization.
"""

from __future__ import annotations

import argparse
import math


def euler_phi(n: int) -> int:
    result = n
    remainder = n
    prime = 2
    while prime * prime <= remainder:
        if remainder % prime == 0:
            while remainder % prime == 0:
                remainder //= prime
            result -= result // prime
        prime += 1
    if remainder > 1:
        result -= result // remainder
    return result


def mobius(n: int) -> int:
    sign = 1
    remainder = n
    prime = 2
    while prime * prime <= remainder:
        if remainder % prime == 0:
            remainder //= prime
            sign = -sign
            if remainder % prime == 0:
                return 0
        prime += 1
    if remainder > 1:
        sign = -sign
    return sign


def ramanujan_sum(q: int, n: int) -> int:
    common = math.gcd(q, n)
    return sum(d * mobius(q // d) for d in range(1, common + 1) if common % d == 0)


def sigma_trunc(cutoff: int, n: int) -> float:
    return sum(
        mobius(q) ** 2 * ramanujan_sum(q, n) / euler_phi(q) ** 2
        for q in range(1, cutoff + 1)
    )


def geometric_kernel_integral(
    n: int, lower: int, q: int, delta: float, subdivisions: int = 4000
) -> float:
    """Integrate the exact balanced geometric kernel on |beta| <= delta/(q*n).

    With x = n*beta and W = n-2*lower+1, the phase-corrected square is

        |sum_{j=0}^{W-1} exp(2*pi*i*j*x/n)|^2 / n.

    Simpson quadrature is sufficient for this feasibility diagnostic. It is not a certificate.
    """
    width = max(0, n - 2 * lower + 1)
    if width == 0:
        return 0.0
    upper = delta / q
    steps = subdivisions + (subdivisions % 2)
    step = upper / steps

    def integrand(x: float) -> float:
        if abs(x) < 1.0e-14:
            return width * width / n
        ratio = math.sin(math.pi * width * x / n) / math.sin(math.pi * x / n)
        return ratio * ratio / n

    total = integrand(0.0) + integrand(upper)
    for index in range(1, steps):
        total += (4 if index % 2 else 2) * integrand(index * step)
    return 2 * step * total / 3


def truncated_model_main(
    cutoff: int, n: int, lower: int, delta: float
) -> float:
    return sum(
        mobius(q) ** 2
        * ramanujan_sum(q, n)
        / euler_phi(q) ** 2
        * geometric_kernel_integral(n, lower, q, delta)
        for q in range(1, cutoff + 1)
    )


def worst_residue_model_mains(
    cutoffs: list[int], n: int, lower: int, delta: float
) -> dict[int, float]:
    """Minimum truncated model over even residue classes for practical small cutoffs."""
    eligible = sorted(set(cutoff for cutoff in cutoffs if cutoff <= 15))
    if not eligible:
        return {}
    max_cutoff = max(eligible)
    period = math.lcm(*range(1, max_cutoff + 1))
    kernels = {
        q: geometric_kernel_integral(n, lower, q, delta)
        for q in range(1, max_cutoff + 1)
    }
    minima = {cutoff: math.inf for cutoff in eligible}
    eligible_set = set(eligible)
    for residue in range(0, period, 2):
        running = 0.0
        for q in range(1, max_cutoff + 1):
            running += (
                mobius(q) ** 2
                * ramanujan_sum(q, residue)
                / euler_phi(q) ** 2
                * kernels[q]
            )
            if q in eligible_set:
                minima[q] = min(minima[q], running)
    return minima


def major_error_bound(n: int, lower: int, delta: float, cutoff: int) -> float:
    upper = n - lower
    width = max(0, n - 2 * lower + 1)
    total = 0.0
    for q in range(1, cutoff + 1):
        phi_q = euler_phi(q)
        beta_radius = delta / (q * n)
        linear_error = q * (
            (0.011 * upper / math.log(lower - 1))
            * (2 * (2 + max(0, upper - (lower - 1)) * 4 * math.pi * beta_radius))
        )
        linear_error += (
            (q + 1) * (int(math.log2(max(upper, 1))) + 1) * math.log(q)
        )
        main_norm = abs(mobius(q)) * width / phi_q
        quadratic_error = linear_error * (2 * main_norm + linear_error)
        total += phi_q * quadratic_error * (2 * delta / (q * n))
    return total


def report(
    n: int,
    lower: int,
    delta: float,
    cutoffs: list[int],
    remainder_ratio: float,
) -> None:
    width = max(0, n - 2 * lower + 1)
    prime_power = 2.5 * (math.isqrt(n) + 1) * math.log(n) ** 2
    worst_mains = worst_residue_model_mains(cutoffs, n, lower, delta)
    print(f"N={n} L={lower} width={width} delta={delta:g}")
    print(
        "Q  sigma_Q       model/N      worst/N      major/N      pp/N         "
        "pre-rem/N     post-rem/N"
    )
    for cutoff in cutoffs:
        sigma_q = sigma_trunc(cutoff, n)
        main = truncated_model_main(cutoff, n, lower, delta)
        worst = worst_mains.get(cutoff, math.nan)
        major = major_error_bound(n, lower, delta, cutoff)
        worst_reserve = worst - major - prime_power
        post_remainder = worst_reserve - remainder_ratio * n
        print(
            f"{cutoff:2d} {sigma_q:12.8f} {main / n:12.8f} {worst / n:12.8f} "
            f"{major / n:12.8f} {prime_power / n:12.8f} {worst_reserve / n:12.8f} "
            f"{post_remainder / n:12.8f}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lower", type=int, default=1_000_001)
    parser.add_argument("--delta", type=float, default=1.0)
    parser.add_argument(
        "--remainder-ratio",
        type=float,
        default=0.0,
        help="diagnostic allowance remainderError(N) = ratio * N",
    )
    parser.add_argument(
        "--cutoffs", type=int, nargs="+", default=[1, 2, 3, 5, 8, 10, 13, 15, 20, 30]
    )
    parser.add_argument(
        "N", type=int, nargs="*", default=[3_000_000, 5_000_000, 10_000_000, 100_000_000]
    )
    args = parser.parse_args()
    for index, n in enumerate(args.N):
        if index:
            print()
        report(n, args.lower, args.delta, args.cutoffs, args.remainder_ratio)


if __name__ == "__main__":
    main()
