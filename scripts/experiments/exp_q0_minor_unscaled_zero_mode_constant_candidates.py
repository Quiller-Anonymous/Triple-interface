#!/usr/bin/env python3
"""
Test simple rational candidates for the intrinsic unscaled post-sigma zero-mode mass scalar.

On the current experiment surface, `sum_by_s_uniform_fast(X)` gives the geometric zero-slice mass
with the surrogate's built-in uniform-window normalization still present. So the order-one
observable tested here is

  rawExactZeroModeMass / (rawGeometricZeroSliceMass * sigma * w(X)^2),

where `w(X) = 1 / (log X * (2H+1))`.
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


CANDIDATES: list[tuple[str, float]] = [
    ("4/3", 4.0 / 3.0),
    ("1", 1.0),
    ("5/4", 5.0 / 4.0),
    ("3/2", 3.0 / 2.0),
]


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


def residual_norm(vals: list[float], target: float) -> float:
    return math.sqrt(sum((x - target) * (x - target) for x in vals))


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Test rational candidates for the unscaled zero-mode mass scalar."
    )
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    rows: dict[str, list[tuple[int, float]]] = {label: [] for label, _ in CANDIDATES}
    fit_rows: list[tuple[int, float]] = []

    for X in Xs:
        exact = sum_by_s(X)
        geom_unscaled = sum_by_s_uniform_fast(X)
        Ns = even_window(X, args.step)

        w = 1.0 / (math.log(X) * (2 * H + 1))
        w2 = w * w
        vals: list[float] = []
        for N in Ns:
            g = geom_unscaled.get(N, 0.0)
            sig = singular_series_shape(N, spf)
            if abs(g) <= 1e-30 or abs(sig) <= 1e-30:
                continue
            vals.append(exact.get(N, 0.0) / (g * sig * w2))

        m = mean(vals)
        std = math.sqrt(variance(vals))
        fit_rows.append((X, m))

        print(f"== X={X:,} ==")
        print(f"mean(unscaled observable) = {m:.12e}")
        print(f"std                      = {std:.12e}")
        for label, target in CANDIDATES:
            rn = residual_norm(vals, target)
            rows[label].append((X, rn))
            print(f"residual norm vs {label:>3s} = {rn:.12e}")
        print()

    if len(Xs) >= 2:
        xs = [x for x, _ in fit_rows]
        ys = [y for _, y in fit_rows]
        print("== Log-Log Exponents ==")
        print(f"mean observable exponent = {fit_loglog_exponent(xs, ys):.6f}")
        for label, vals in rows.items():
            ys2 = [y for _, y in vals]
            print(f"residual exponent vs {label:>3s} = {fit_loglog_exponent(xs, ys2):.6f}")


if __name__ == "__main__":
    main()
