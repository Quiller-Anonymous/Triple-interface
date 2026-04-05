#!/usr/bin/env python3
"""
Layer-by-layer provenance diagnostic for the zero-mode constant.

For each `X`, this script prints the dense-window statistics of the successive normalized ratios:

1. zeroModeScalar
2. zeroModeScalar / q0NormFactor(N)
3. zeroModeScalar / (q0NormFactor(N) * geometricWeightedMinorCoeff(X,N,0))
4. zeroModeScalar / (q0NormFactor(N) * geometricWeightedMinorCoeff(X,N,0) * sigma(N))
5. zeroModeScalar / (q0NormFactor(N) * geometricWeightedMinorCoeff(X,N,0) * sigma(N) * c_X)

The goal is to see at which stage the quantity becomes approximately constant in `N` and nearly
stable in `X`.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import H, Q0, WeightBackend, mobius_phi_sieve, q0_norm_factor, sum_by_s
from exp_q0_minor_zero_mode_refinement import even_window, fit_loglog_exponent, singular_series_shape, smallest_prime_factors, sum_by_s_uniform_fast


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


def variance(xs: list[float]) -> float:
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs) / len(xs)


def summarize(label: str, vals: list[float]) -> tuple[float, float]:
    m = mean(vals)
    std = math.sqrt(variance(vals))
    cv = 0.0 if abs(m) <= 1e-30 else std / abs(m)
    print(f"{label:24s} mean={m:.12e}  std={std:.12e}  cv={cv:.12e}")
    return m, cv


def main() -> None:
    parser = argparse.ArgumentParser(description="Zero-mode constant provenance by normalization layers.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    parser.add_argument("--cut", type=float, default=1e-30)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    final_mean_rows: list[tuple[int, float]] = []
    final_cv_rows: list[tuple[int, float]] = []

    for X in Xs:
        Ns = even_window(X, args.step)
        prime_by_s = sum_by_s(X)
        geom_by_s = sum_by_s_uniform_fast(X)
        cX = route_window_floor(X)

        mu_q0, phi_q0 = mobius_phi_sieve(Q0)
        backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
        w0 = backend.minor_weight(0)

        lvl0: list[float] = []
        lvl1: list[float] = []
        lvl2: list[float] = []
        lvl3: list[float] = []
        lvl4: list[float] = []

        for N in Ns:
            zero = q0_norm_factor(N) * prime_by_s.get(N, 0.0) * w0
            q0 = q0_norm_factor(N)
            geom0 = q0_norm_factor(N) * geom_by_s.get(N, 0.0) * w0
            sigma = singular_series_shape(N, spf)

            lvl0.append(zero)
            if abs(q0) > args.cut:
                lvl1.append(zero / q0)
            if abs(geom0) > args.cut:
                lvl2.append(zero / geom0)
            if abs(geom0) > args.cut and abs(sigma) > args.cut:
                lvl3.append(zero / (geom0 * sigma))
            if abs(geom0) > args.cut and abs(sigma) > args.cut and abs(cX) > args.cut:
                lvl4.append(zero / (geom0 * sigma * cX))

        print(f"== X={X:,} ==")
        print(f"dense_even_window_size={len(Ns)}")
        print(f"c_X={cX:.12e}")
        print()
        summarize("zero", lvl0)
        summarize("zero / q0", lvl1)
        summarize("zero / (q0*geom0)", lvl2)
        summarize("zero / (...*sigma)", lvl3)
        m4, cv4 = summarize("zero / (...*sigma*c_X)", lvl4)
        final_mean_rows.append((X, m4))
        final_cv_rows.append((X, cv4))
        print()

    if len(final_mean_rows) >= 2:
        xs = [x for x, _ in final_mean_rows]
        means = [m for _, m in final_mean_rows]
        cvs = [c for _, c in final_cv_rows]
        print("== Log-Log Exponents ==")
        print(f"final layer mean exponent      = {fit_loglog_exponent(xs, means):.6f}")
        print(f"final layer cv exponent        = {fit_loglog_exponent(xs, cvs):.6f}")


if __name__ == "__main__":
    main()
