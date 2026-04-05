#!/usr/bin/env python3
"""
Compare exact zero-mode numerator and geometric zero baseline under matched slice conventions.

This script avoids post hoc scalar rescaling and instead computes the bookkeeping constant under a
small fixed list of explicit aggregation conventions:

- pointwise mean of ratios over the dense even window,
- ratio of dense-even sums,
- ratio of dense-even trapezoidal sums,
- full-window mean after extending odd entries by zero,
- symmetry-adjusted ratio of sums.

The goal is to determine whether the remaining scalar really comes from a sum-vs-mean or support
counting convention, rather than from arithmetic shape.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import H, Q0, WeightBackend, mobius_phi_sieve, q0_norm_factor, sum_by_s
from exp_q0_minor_zero_mode_refinement import even_window, singular_series_shape, smallest_prime_factors, sum_by_s_uniform_fast


def parse_x_list(spec: str) -> list[int]:
    out: list[int] = []
    for piece in spec.split(","):
        piece = piece.strip()
        if piece:
            out.append(int(piece))
    if not out:
        raise SystemExit("empty --X-list")
    return out


def route_window_floor(X: int) -> float:
    return (1.0 / 800.0) * (1.0 / (math.log(X + H) ** 2))


def mean(xs: list[float]) -> float:
    return sum(xs) / len(xs)


def weighted_sum(xs: list[float], endpoint_half: bool) -> float:
    if not xs:
        return 0.0
    if not endpoint_half or len(xs) == 1:
        return sum(xs)
    return 0.5 * xs[0] + sum(xs[1:-1]) + 0.5 * xs[-1]


def safe_ratio(num: float, den: float) -> float:
    return 0.0 if abs(den) <= 1e-30 else num / den


def main() -> None:
    parser = argparse.ArgumentParser(description="Zero-mode slice-convention comparison.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    for X in Xs:
        Ns_even = even_window(X, args.step)
        cX = route_window_floor(X)

        prime_by_s = sum_by_s(X)
        geom_by_s = sum_by_s_uniform_fast(X)

        mu_q0, phi_q0 = mobius_phi_sieve(Q0)
        backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
        w0 = backend.minor_weight(0)

        zero_even: list[float] = []
        base_even: list[float] = []
        pointwise_ratios: list[float] = []

        for N in Ns_even:
            zero = q0_norm_factor(N) * prime_by_s.get(N, 0.0) * w0
            geom0 = q0_norm_factor(N) * geom_by_s.get(N, 0.0) * w0
            sigma = singular_series_shape(N, spf)
            base = geom0 * sigma * cX
            zero_even.append(zero)
            base_even.append(base)
            if abs(base) > 1e-30:
                pointwise_ratios.append(zero / base)

        dense_even_sum_ratio = safe_ratio(sum(zero_even), sum(base_even))
        dense_even_trap_ratio = safe_ratio(
            weighted_sum(zero_even, endpoint_half=True),
            weighted_sum(base_even, endpoint_half=True),
        )

        # Extend by zero to the full [X, X+H] window.
        zero_full = [0.0] * (H + 1)
        base_full = [0.0] * (H + 1)
        idx_map = {N - X: i for i, N in enumerate(Ns_even)}
        for j in range(H + 1):
            if j in idx_map:
                i = idx_map[j]
                zero_full[j] = zero_even[i]
                base_full[j] = base_even[i]

        full_window_mean_ratio = safe_ratio(mean(zero_full), mean(base_full))
        symmetry_adjusted_sum_ratio = safe_ratio(sum(zero_even), 0.5 * sum(base_even))

        print(f"== X={X:,} ==")
        print(f"dense_even_count={len(Ns_even)} full_window_count={H + 1}")
        print(f"pointwise mean of ratios      = {mean(pointwise_ratios):.12e}")
        print(f"ratio of dense-even sums      = {dense_even_sum_ratio:.12e}")
        print(f"ratio of dense-even trap sums = {dense_even_trap_ratio:.12e}")
        print(f"ratio of full-window means    = {full_window_mean_ratio:.12e}")
        print(f"symmetry-adjusted sum ratio   = {symmetry_adjusted_sum_ratio:.12e}")
        print()


if __name__ == "__main__":
    main()
