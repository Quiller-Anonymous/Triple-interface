#!/usr/bin/env python3
"""
Raw zero-mode mass comparison between the exact numerator and the geometric zero baseline.

This strips away the later route-facing layers and compares:

- exact raw zero-mode mass: `sum_by_s(X)[N]`
- raw interval-convolution zero-slice mass: `sum_by_s_uniform_fast(X)[N]`

The goal is to keep a reproducible record of the remaining upstream seam before `q0`, `w0`,
`sigma`, and `c_X` are imposed.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import H, sum_by_s
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


def mean(xs: list[float]) -> float:
    return sum(xs) / len(xs)


def variance(xs: list[float]) -> float:
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs) / len(xs)


def summarize(label: str, vals: list[float]) -> None:
    m = mean(vals)
    std = math.sqrt(variance(vals))
    cv = 0.0 if abs(m) <= 1e-30 else std / abs(m)
    print(f"{label:28s} mean={m:.12e}  std={std:.12e}  cv={cv:.12e}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Raw zero-mode mass comparison.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    for X in Xs:
        exact = sum_by_s(X)
        geom = sum_by_s_uniform_fast(X)
        Ns = even_window(X, args.step)

        ratio_raw: list[float] = []
        ratio_sigma: list[float] = []
        for N in Ns:
            g = geom.get(N, 0.0)
            if abs(g) <= 1e-30:
                continue
            ratio_raw.append(exact.get(N, 0.0) / g)
            ratio_sigma.append(exact.get(N, 0.0) / (g * singular_series_shape(N, spf)))

        w_scale = 1.0 / (math.log(X) * (2 * H + 1))
        print(f"== X={X:,} ==")
        print(f"uniform window scalar weight = {w_scale:.12e}")
        print(f"uniform window scalar sq     = {w_scale * w_scale:.12e}")
        print()
        summarize("exact/geom raw", ratio_raw)
        summarize("exact/(geom*sigma)", ratio_sigma)
        print()


if __name__ == "__main__":
    main()
