#!/usr/bin/env python3
"""
Candidate comparison on the half-mass-recentered zero-mode observable.

This tests the corrected order-one object

  rawExactZeroModeMass / ((1/2) * w(X)^2 * sigma),

against a short fixed list of scalar candidates:
- 4/3
- 5/4
- the empirical three-point mean 1.325228687827
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
EMPIRICAL_MEAN = 1.325228687827
CANDIDATES: list[tuple[str, float]] = [
    ("4/3", 4.0 / 3.0),
    ("5/4", 5.0 / 4.0),
    ("empirical", EMPIRICAL_MEAN),
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


def residual_norm(vals: list[float], target: float) -> float:
    return math.sqrt(sum((x - target) * (x - target) for x in vals))


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Candidate comparison for the half-mass-recentered observable."
    )
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)
    rows: dict[str, list[tuple[int, float]]] = {label: [] for label, _ in CANDIDATES}

    for X in Xs:
        exact = sum_by_s(X)
        geom = sum_by_s_uniform_fast(X)
        Ns = even_window(X, args.step)
        w = 1.0 / (math.log(X) * (2 * H + 1))
        w2 = w * w

        vals: list[float] = []
        for N in Ns:
            g = geom.get(N, 0.0)
            sig = singular_series_shape(N, spf)
            if abs(g) <= 1e-30 or abs(sig) <= 1e-30:
                continue
            vals.append(exact.get(N, 0.0) / (HALF_MASS * w2 * sig))

        print(f"== X={X:,} ==")
        print(f"mean(recentered observable) = {mean(vals):.12e}")
        for label, target in CANDIDATES:
            rn = residual_norm(vals, target)
            rows[label].append((X, rn))
            print(f"residual norm vs {label:>9s} = {rn:.12e}")
        print()

    if len(Xs) >= 2:
        xs = [x for x, _ in next(iter(rows.values()))]
        print("== Log-Log Exponents ==")
        for label, vals in rows.items():
            ys = [y for _, y in vals]
            print(f"residual exponent vs {label:>9s} = {fit_loglog_exponent(xs, ys):.6f}")


if __name__ == "__main__":
    main()
