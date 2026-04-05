#!/usr/bin/env python3
"""
Compare the raw exact zero-mode mass against the unscaled surrogate zero-slice mass.

This is the upstream provenance diagnostic after removing the singular-series `N`-shape:

  rawExactZeroModeMass / (unscaledGeometricZeroSliceMass * sigma)

It also divides by the surrogate's built-in uniform-window normalization square

  (1 / (log X * (2H+1)))^2

to see how much of the remaining scalar is already explained by the intrinsic surrogate mass
normalization.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import H, sum_by_s
from exp_q0_minor_zero_mode_refinement import (
    even_window,
    singular_series_shape,
    smallest_prime_factors,
    sum_by_s_uniform_fast,
)


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


def summarize(label: str, vals: list[float]) -> None:
    m = mean(vals)
    std = math.sqrt(variance(vals))
    cv = 0.0 if abs(m) <= 1e-30 else std / abs(m)
    print(f"{label:34s} mean={m:.12e}  std={std:.12e}  cv={cv:.12e}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compare raw exact zero mass against the unscaled surrogate zero-slice mass."
    )
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    for X in Xs:
        exact = sum_by_s(X)
        geom_unscaled = sum_by_s_uniform_fast(X)
        Ns = even_window(X, args.step)
        w = 1.0 / (math.log(X) * (2 * H + 1))
        w2 = w * w

        ratio_unscaled_sigma: list[float] = []
        ratio_div_w2: list[float] = []
        for N in Ns:
            g = geom_unscaled.get(N, 0.0)
            sig = singular_series_shape(N, spf)
            if abs(g) <= 1e-30 or abs(sig) <= 1e-30:
                continue
            r = exact.get(N, 0.0) / (g * sig)
            ratio_unscaled_sigma.append(r)
            ratio_div_w2.append(r / w2)

        print(f"== X={X:,} ==")
        print(f"uniform window normalization     = {w:.12e}")
        print(f"uniform window normalization^2   = {w2:.12e}")
        summarize("exact/(unscaled_geom*sigma)", ratio_unscaled_sigma)
        summarize("exact/(unscaled_geom*sigma*w^2)", ratio_div_w2)
        print()


if __name__ == "__main__":
    main()
