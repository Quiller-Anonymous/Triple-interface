#!/usr/bin/env python3
"""
Residual-correlation diagnostic for the half-mass-recentered zero-mode observable.

This studies

  r_{4/3}(X,N) = halfMassRecenteredZeroModeObservable(X,N) - 4/3

against a short list of upstream zero-slice support statistics:
- support size defect
- boundary mass defect
- diagonal share
- zero-slice support asymmetry

If these statistics are constant or essentially uncorrelated with the residual, that is strong
evidence that the remaining variation is just small noise around a genuine scalar.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import H, Ucut, sum_by_s
from exp_q0_minor_zero_mode_refinement import (
    even_window,
    singular_series_shape,
    smallest_prime_factors,
    sum_by_s_uniform_fast,
)
TARGET = 4.0 / 3.0
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


def corr(xs: list[float], ys: list[float]) -> str:
    vx = variance(xs)
    vy = variance(ys)
    if vx <= 1e-30 or vy <= 1e-30:
        return "constant"
    mx = mean(xs)
    my = mean(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = math.sqrt(sum((x - mx) ** 2 for x in xs) * sum((y - my) ** 2 for y in ys))
    return f"{num / den:.12e}"


def k_full(k: int) -> float:
    if abs(k) > H:
        return 0.0
    return max(1.0 - abs(k) / float(Ucut), 0.0) / float(Ucut)


def support_radius(X: int, N: int) -> int:
    lo = X - 2 * H
    hi = X + 2 * H
    return min(H, N - lo, hi - N)


def support_size_even_radius(M: int) -> int:
    return 2 * (M // 2) + 1


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Residual correlation against upstream zero-slice support statistics."
    )
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)
    k0 = k_full(0)

    for X in Xs:
        exact = sum_by_s(X)
        geom = sum_by_s_uniform_fast(X)
        Ns = even_window(X, args.step)
        w = 1.0 / (math.log(X) * (2 * H + 1))
        w2 = w * w

        residuals: list[float] = []
        support_size_defect: list[float] = []
        boundary_mass_defect: list[float] = []
        diagonal_share: list[float] = []
        asymmetry: list[float] = []

        raw_support_sizes: list[float] = []
        raw_boundary_defects: list[float] = []
        raw_diag_shares: list[float] = []
        raw_asymmetries: list[float] = []

        for N in Ns:
            sig = singular_series_shape(N, spf)
            g = geom.get(N, 0.0)
            if abs(sig) <= 1e-30 or abs(g) <= 1e-30:
                continue

            obs = exact.get(N, 0.0) / (HALF_MASS * w2 * sig)
            residuals.append(obs - TARGET)

            M = support_radius(X, N)
            sz = float(support_size_even_radius(M))
            raw_support_sizes.append(sz)

            bdef = HALF_MASS - g
            raw_boundary_defects.append(bdef)

            dshare = k0 / g
            raw_diag_shares.append(dshare)

            # By symmetry this should be zero, but we keep it explicit as a diagnostic.
            pos_mass = sum(k_full(d) for d in range(2, M + 1, 2))
            neg_mass = pos_mass
            asym = (pos_mass - neg_mass) / g
            raw_asymmetries.append(asym)

        mean_sz = mean(raw_support_sizes)
        mean_bd = mean(raw_boundary_defects)
        mean_diag = mean(raw_diag_shares)
        mean_asym = mean(raw_asymmetries)

        support_size_defect = [x - mean_sz for x in raw_support_sizes]
        boundary_mass_defect = [x - mean_bd for x in raw_boundary_defects]
        diagonal_share = [x - mean_diag for x in raw_diag_shares]
        asymmetry = [x - mean_asym for x in raw_asymmetries]

        print(f"== X={X:,} ==")
        print(f"mean residual vs 4/3             = {mean(residuals):.12e}")
        print(f"corr(residual, support size)     = {corr(residuals, support_size_defect)}")
        print(f"corr(residual, boundary defect)  = {corr(residuals, boundary_mass_defect)}")
        print(f"corr(residual, diagonal share)   = {corr(residuals, diagonal_share)}")
        print(f"corr(residual, asymmetry)        = {corr(residuals, asymmetry)}")
        print(
            f"variances: size={variance(support_size_defect):.12e} "
            f"boundary={variance(boundary_mass_defect):.12e} "
            f"diag={variance(diagonal_share):.12e} "
            f"asym={variance(asymmetry):.12e}"
        )
        print()


if __name__ == "__main__":
    main()
