#!/usr/bin/env python3
"""
Zero-mode normalization diagnostic for the fixed-formula bridge witness.

For the current theorem surface

  SS_formula(X,N)
    = q0_norm_factor(N) * geometricWeightedMinorCoeff(X,N,0) * Sigma(X,N),

this script studies the normalized zero observable

  Z(X,N) = zeroModeScalar(X,N)
           / (q0_norm_factor(N) * geometricWeightedMinorCoeff(X,N,0))

on the dense even window `N in [X, X+H]`.

The immediate comparison target is the current arithmetic core

  Sigma(X,N) = singular_series_shape(N).

The purpose is to decide between:

1. global-envelope error: `Z / sigma` is approximately constant in `N`,
2. local-shape error: `Z / sigma` has substantial `N`-dependence.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import (
    H,
    Q0,
    WeightBackend,
    mobius_phi_sieve,
    q0_norm_factor,
    sum_by_s,
)
from exp_q0_minor_zero_mode_refinement import (
    corr,
    even_window,
    fit_loglog_exponent,
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


def main() -> None:
    parser = argparse.ArgumentParser(description="Normalized zero-mode sigma diagnostic.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    parser.add_argument(
        "--denom-cut",
        type=float,
        default=1e-30,
        help="discard points where |q0*geom0| is below this threshold",
    )
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    envelope_rows: list[tuple[int, float]] = []
    ratio_dispersion_rows: list[tuple[int, float]] = []
    sigma_residual_rows: list[tuple[int, float]] = []

    for X in Xs:
        Ns = even_window(X, args.step)
        prime_by_s = sum_by_s(X)
        geom_by_s = sum_by_s_uniform_fast(X)

        mu_q0, phi_q0 = mobius_phi_sieve(Q0)
        backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
        w0 = backend.minor_weight(0)

        kept_Ns: list[int] = []
        z_vals: list[float] = []
        sigma_vals: list[float] = []
        ratio_vals: list[float] = []

        for N in Ns:
            zero_exact = q0_norm_factor(N) * prime_by_s.get(N, 0.0) * w0
            geom0 = q0_norm_factor(N) * geom_by_s.get(N, 0.0) * w0
            if abs(geom0) <= args.denom_cut:
                continue
            z = zero_exact / geom0
            sigma = singular_series_shape(N, spf)
            kept_Ns.append(N)
            z_vals.append(z)
            sigma_vals.append(sigma)
            ratio_vals.append(z / sigma if abs(sigma) > 1e-30 else 0.0)

        if not kept_Ns:
            print(f"== X={X:,} ==")
            print("no points passed denominator cutoff")
            print()
            continue

        sigma_dot_sigma = sum(s * s for s in sigma_vals)
        envelope = 0.0 if sigma_dot_sigma == 0.0 else sum(
            z * s for z, s in zip(z_vals, sigma_vals)
        ) / sigma_dot_sigma
        sigma_fit_residual = [z - envelope * s for z, s in zip(z_vals, sigma_vals)]
        sigma_fit_residual_norm = math.sqrt(sum(r * r for r in sigma_fit_residual))
        ratio_mean = mean(ratio_vals)
        ratio_std = math.sqrt(variance(ratio_vals))
        ratio_cv = 0.0 if abs(ratio_mean) <= 1e-30 else ratio_std / abs(ratio_mean)

        envelope_rows.append((X, envelope))
        ratio_dispersion_rows.append((X, ratio_cv))
        sigma_residual_rows.append((X, sigma_fit_residual_norm))

        print(f"== X={X:,} ==")
        print(f"dense_even_window_size={len(Ns)}")
        print(f"kept_points={len(kept_Ns)}")
        print()
        print("-- normalized zero observable --")
        print(f"mean(Z)                    = {mean(z_vals):.12e}")
        print(f"mean(sigma)                = {mean(sigma_vals):.12e}")
        print(f"corr(Z, sigma)             = {corr(z_vals, sigma_vals):.6f}")
        print()
        print("-- envelope test --")
        print(f"best envelope E(X)         = {envelope:.12e}")
        print(f"std(Z/sigma)               = {ratio_std:.12e}")
        print(f"cv(Z/sigma)                = {ratio_cv:.12e}")
        print(f"||Z - E(X)*sigma||_2       = {sigma_fit_residual_norm:.12e}")
        print()
        print("-- sample points --")
        sample_idx = sorted(set([0, len(kept_Ns) // 2, len(kept_Ns) - 1]))
        for idx in sample_idx:
            N = kept_Ns[idx]
            print(
                f"N={N}: Z={z_vals[idx]:.12e} sigma={sigma_vals[idx]:.12e} "
                f"Z/sigma={ratio_vals[idx]:.12e}"
            )
        print()

    if len(Xs) >= 2 and envelope_rows:
        xs = [x for x, _ in sigma_residual_rows]
        sigma_residuals = [y for _, y in sigma_residual_rows]
        ratio_cvs = [y for _, y in ratio_dispersion_rows]
        print("== Log-Log Exponents ==")
        print(f"||Z - E(X)*sigma||_2 exponent = {fit_loglog_exponent(xs, sigma_residuals):.6f}")
        print(f"cv(Z/sigma) exponent         = {fit_loglog_exponent(xs, ratio_cvs):.6f}")


if __name__ == "__main__":
    main()
