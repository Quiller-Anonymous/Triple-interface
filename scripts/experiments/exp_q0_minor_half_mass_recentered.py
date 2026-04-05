#!/usr/bin/env python3
"""
Half-mass diagnostics for the unscaled geometric zero slice and the recentered zero-mode observable.

This measures two quantities on the dense even window:

1. unscaledGeometricZeroSliceMass - 1/2
2. rawExactZeroModeMass / ((1/2) * w(X)^2 * sigma)

The goal is to test whether the moving unscaled surrogate zero slice has already collapsed to a
fixed half-mass baseline, and whether the raw observable recentered with that half-mass baseline
plus the surrogate normalization square is then close to a fixed order-one scalar.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import H, sum_by_s
from exp_q0_minor_zero_mode_refinement import (
    even_window,
    fit_loglog_exponent,
    singular_series_shape,
    smallest_prime_factors,
    sum_by_s_uniform_fast,
)


HALF_MASS = 0.5


def parse_x_list(spec: str) -> list[int]:
    out: list[int] = []
    for piece in spec.split(","):
        piece = piece.strip()
        if piece:
            out.append(int(piece))
    if not out:
        raise SystemExit("empty --X-list")
    return out


def mean(xs: list[float]) -> float:
    return sum(xs) / len(xs)


def variance(xs: list[float]) -> float:
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs) / len(xs)


def l2_norm(xs: list[float]) -> float:
    return math.sqrt(sum(x * x for x in xs))


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Half-mass diagnostics for the unscaled geometric zero slice."
    )
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    half_rows: list[tuple[int, float]] = []
    recentered_rows: list[tuple[int, float]] = []

    for X in Xs:
        exact = sum_by_s(X)
        geom = sum_by_s_uniform_fast(X)
        Ns = even_window(X, args.step)
        w = 1.0 / (math.log(X) * (2 * H + 1))
        w2 = w * w

        half_errs: list[float] = []
        recentered_vals: list[float] = []

        for N in Ns:
            g = geom.get(N, 0.0)
            sig = singular_series_shape(N, spf)
            if abs(sig) <= 1e-30:
                continue
            half_errs.append(g - HALF_MASS)
            rec = exact.get(N, 0.0) / (HALF_MASS * w2 * sig)
            recentered_vals.append(rec)

        half_norm = l2_norm(half_errs)
        recentered_mean = mean(recentered_vals)
        recentered_errs = [x - recentered_mean for x in recentered_vals]
        recentered_norm = l2_norm(recentered_errs)
        half_rows.append((X, half_norm))
        recentered_rows.append((X, recentered_norm))

        print(f"== X={X:,} ==")
        print(f"mean(unscaled geom)           = {mean([geom[N] for N in Ns]):.12e}")
        print(f"std(unscaled geom)            = {math.sqrt(variance([geom[N] for N in Ns])):.12e}")
        print(f"||geom - 1/2||_2              = {half_norm:.12e}")
        print(f"mean(recentered observable)   = {recentered_mean:.12e}")
        print(f"std(recentered observable)    = {math.sqrt(variance(recentered_vals)):.12e}")
        print(f"||recentered - mean||_2       = {recentered_norm:.12e}")
        print()

    if len(Xs) >= 2:
        xs = [x for x, _ in half_rows]
        half_vals = [y for _, y in half_rows]
        rec_vals = [y for _, y in recentered_rows]
        print("== Log-Log Exponents ==")
        print(f"||geom - 1/2||_2 exponent       = {fit_loglog_exponent(xs, half_vals):.6f}")
        print(f"||recentered - mean||_2 exponent = {fit_loglog_exponent(xs, rec_vals):.6f}")


if __name__ == "__main__":
    main()
