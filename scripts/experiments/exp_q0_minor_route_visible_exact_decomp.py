#!/usr/bin/env python3
"""
Exact fixed-formula decomposition of the route-visible scalar.

This script fixes one explicit candidate bridge decomposition

  routeVisible = G + SS + R

where:

- `G` is the fixed geometric mean-channel model built from the explicit interval-convolution surrogate,
- `SS` is the fixed full singular-series zero-mode formula on the geometric zero mode,
- `R` is the exact residual.

No regression coefficients are used in the definitions. This keeps the witness roles explicit:

- exact witness: routeVisible
- fixed candidate bridge model: G + SS
- residual: R

The output compares the residual directly against the normalized route-style threshold

  c_X^2 * (H / X + 1 / (H * Q0^2))

on the fixed-`H` exact surface.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import (
    H,
    Q0,
    WeightBackend,
    build_weighted_slices,
    cache_path,
    canonical_window_points,
    dot,
    ensure_weights,
    mobius_phi_sieve,
    q0_norm_factor,
    sum_by_s,
)
from exp_q0_minor_zero_mode_refinement import (
    even_window,
    fit_loglog_exponent,
    singular_series_shape,
    smallest_prime_factors,
)
from exp_q0_minor_zero_mode_refinement import sum_by_s_uniform_fast


def parse_x_list(spec: str) -> list[int]:
    out: list[int] = []
    for piece in spec.split(","):
        piece = piece.strip()
        if piece:
            out.append(int(piece))
    if not out:
        raise SystemExit("empty --X-list")
    return out


def route_bound_fixed_h(X: int) -> float:
    return H / float(X) + 1.0 / (H * (Q0 ** 2))


def route_norm_floor_sq(X: int) -> float:
    return ((1.0 / 800.0) * (1.0 / (math.log(X + H) ** 2))) ** 2


def normalized_route_budget(X: int) -> float:
    return route_norm_floor_sq(X) * route_bound_fixed_h(X)


SIGMA_ENVELOPE_KAPPA = 4.089173283623e-04


def sigma_envelope_formula(X: int) -> float:
    return SIGMA_ENVELOPE_KAPPA / (math.log(X + H) ** 2)


def main() -> None:
    parser = argparse.ArgumentParser(description="Exact calibrated G + SS + R decomposition on the route-visible scalar.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--dense-step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    residual_norm_rows: list[tuple[int, float]] = []
    residual_ratio_rows: list[tuple[int, float]] = []
    zero_ratio_rows: list[tuple[int, float]] = []
    mean_ratio_rows: list[tuple[int, float]] = []

    for X in Xs:
        sparse_window = canonical_window_points(X)
        dense_window = even_window(X, args.dense_step)

        prime_by_s = sum_by_s(X)
        geom_by_s = sum_by_s_uniform_fast(X)

        mu_q0, phi_q0 = mobius_phi_sieve(Q0)
        backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
        weights = ensure_weights(
            required_abs_t=range(0, X + 2 * H + 1),
            backend=backend,
            jobs=1,
            cache_file=cache_path(X, "exact", None),
        )

        prime_slices = build_weighted_slices(X, sparse_window, weights, prime_by_s)
        geom_slices = build_weighted_slices(X, sparse_window, weights, geom_by_s)

        # Exact sparse route-visible scalar and its fixed geometric model.
        route_exact = [sl.raw0 + sl.nonzero_sum for sl in prime_slices]
        zero_exact = [sl.raw0 for sl in prime_slices]
        mean_exact = [sl.nonzero_sum for sl in prime_slices]
        G_zero_sparse = [sl.raw0 for sl in geom_slices]
        G_mean_sparse = [sl.nonzero_sum for sl in geom_slices]
        scale_sparse = [q0_norm_factor(N) for N in sparse_window]
        G_sparse = [scale * gm for scale, gm in zip(scale_sparse, G_mean_sparse)]

        # Fixed singular-series zero-mode formula on the geometric zero mode.
        sigma_sparse = [singular_series_shape(N, spf) for N in sparse_window]
        env = sigma_envelope_formula(X)
        SS_sparse = [
            scale * g0 * env * sig
            for scale, g0, sig in zip(scale_sparse, G_zero_sparse, sigma_sparse)
        ]

        R_sparse = [
            rv - g - ss for rv, g, ss in zip(route_exact, G_sparse, SS_sparse)
        ]
        zero_err_sparse = [z - ss for z, ss in zip(zero_exact, SS_sparse)]
        mean_err_sparse = [m - g for m, g in zip(mean_exact, G_sparse)]

        residual_energy = dot(R_sparse, R_sparse)
        residual_norm = math.sqrt(residual_energy)
        zero_energy = dot(zero_err_sparse, zero_err_sparse)
        mean_energy = dot(mean_err_sparse, mean_err_sparse)
        raw_bound = route_bound_fixed_h(X)
        floor_sq = route_norm_floor_sq(X)
        budget = normalized_route_budget(X)
        ratio = residual_energy / budget
        zero_ratio = zero_energy / budget
        mean_ratio = mean_energy / budget

        residual_norm_rows.append((X, residual_norm))
        residual_ratio_rows.append((X, ratio))
        zero_ratio_rows.append((X, zero_ratio))
        mean_ratio_rows.append((X, mean_ratio))

        model_energy = dot(G_sparse, G_sparse) + dot(SS_sparse, SS_sparse)
        full_energy = dot(route_exact, route_exact)
        reconstruction_error = max(
            abs(a - b - c - d)
            for a, b, c, d in zip(route_exact, G_sparse, SS_sparse, R_sparse)
        )

        print(f"== X={X:,} ==")
        print(f"sparse_window={sparse_window}")
        print(f"dense_window_size={len(dense_window)}")
        print()
        print("-- fixed formulas --")
        print("G = q0_norm_factor(N) * frozen geometric mean-channel scalar")
        print(
            "SS = q0_norm_factor(N) * geometric zero-mode scalar * "
            "sigma_envelope_formula(X) * singular_series_shape(N)"
        )
        print(f"sigma_envelope_formula(X) = {env:.12e}")
        print()
        print("-- energy ledger --")
        print(f"routeVisible energy = {full_energy:.12e}")
        print(f"G+SS model energy   = {model_energy:.12e}")
        print(f"residual energy     = {residual_energy:.12e}")
        print(f"residual norm       = {residual_norm:.12e}")
        print(f"route_bound raw     = {raw_bound:.12e}")
        print(f"norm floor sq       = {floor_sq:.12e}")
        print(f"normalized budget   = {budget:.12e}")
        print(f"residual/budget     = {ratio:.12e}")
        print(f"reconstruction max error = {reconstruction_error:.12e}")
        print()
        print("-- channel isolation --")
        print(f"||zero - SS||^2 / budget      = {zero_ratio:.12e}")
        print(f"||mean - G||^2 / budget       = {mean_ratio:.12e}")
        print(
            f"cross-cancellation factor = {residual_norm / (math.sqrt(zero_energy) + math.sqrt(mean_energy)):.12e}"
        )
        print()
        print("-- sparse decomposition by N --")
        for N, rv, z, m, g0, gm, g, ss, r in zip(
            sparse_window,
            route_exact,
            zero_exact,
            mean_exact,
            G_zero_sparse,
            G_mean_sparse,
            G_sparse,
            SS_sparse,
            R_sparse,
        ):
            print(
                f"N={N}: route={rv:.12e} zero={z:.12e} mean={m:.12e} "
                f"G0={g0:.12e} Gm={gm:.12e} G={g:.12e} SS={ss:.12e} R={r:.12e}"
            )
        print()

    if len(Xs) >= 2:
        xs = [x for x, _ in residual_norm_rows]
        residual_norms = [y for _, y in residual_norm_rows]
        residual_ratios = [y for _, y in residual_ratio_rows]
        zero_ratios = [y for _, y in zero_ratio_rows]
        mean_ratios = [y for _, y in mean_ratio_rows]
        print("== Log-Log Exponents ==")
        print(f"residual norm exponent       = {fit_loglog_exponent(xs, residual_norms):.6f}")
        print(f"residual/budget exponent     = {fit_loglog_exponent(xs, residual_ratios):.6f}")
        print(f"zero-vs-SS exponent          = {fit_loglog_exponent(xs, zero_ratios):.6f}")
        print(f"mean-vs-G exponent           = {fit_loglog_exponent(xs, mean_ratios):.6f}")


if __name__ == "__main__":
    main()
