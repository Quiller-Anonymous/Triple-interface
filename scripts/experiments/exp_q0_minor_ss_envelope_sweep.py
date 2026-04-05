#!/usr/bin/env python3
"""
Envelope sweep for the zero-mode arithmetic core in the fixed-formula bridge witness.

We keep

  G_formula(X,N) = q0_norm_factor(N) * geometricMeanChannelScalar(X,N)

fixed, and test short explicit envelope candidates in

  SS_formula(X,N)
    = q0_norm_factor(N) * geometricZeroMode(X,N) * E_formula(X) * sigma(N).

Each candidate gets a single global scalar `kappa`, fitted once across the whole sampled grid.
The scoring is route-facing only:

* zero-side ratio   = ||zero - SS||^2 / budget
* total residual    = ||R||^2 / budget
* log-log slopes in X of both quantities
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

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
    fit_loglog_exponent,
    singular_series_shape,
    smallest_prime_factors,
    sum_by_s_uniform_fast,
)


@dataclass(frozen=True)
class EnvelopeCandidate:
    name: str
    label: str

    def base(self, X: int) -> float:
        if self.name == "log_x_plus_h_inv2":
            return 1.0 / (math.log(X + H) ** 2)
        if self.name == "log_x_inv2":
            return 1.0 / (math.log(X) ** 2)
        if self.name == "log_x_plus_half_h_inv2":
            return 1.0 / (math.log(X + H / 2.0) ** 2)
        if self.name == "x_neg_one_sixth":
            return X ** (-1.0 / 6.0)
        raise ValueError(f"unknown candidate {self.name}")


CANDIDATES = [
    EnvelopeCandidate("log_x_plus_h_inv2", "kappa / log(X+H)^2"),
    EnvelopeCandidate("log_x_inv2", "kappa / log(X)^2"),
    EnvelopeCandidate("log_x_plus_half_h_inv2", "kappa / log(X+H/2)^2"),
    EnvelopeCandidate("x_neg_one_sixth", "kappa * X^(-1/6)"),
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


def route_bound_fixed_h(X: int) -> float:
    return H / float(X) + 1.0 / (H * (Q0 ** 2))


def route_norm_floor_sq(X: int) -> float:
    return ((1.0 / 800.0) * (1.0 / (math.log(X + H) ** 2))) ** 2


def normalized_route_budget(X: int) -> float:
    return route_norm_floor_sq(X) * route_bound_fixed_h(X)


def fit_global_kappa(candidate: EnvelopeCandidate, rows: list[tuple[int, float, float]]) -> float:
    # rows are (X, target, sigma_weighted_geom0) and we fit target ≈ kappa * base(X) * sigma_weighted_geom0
    denom = 0.0
    numer = 0.0
    for X, target, sigma_geom in rows:
        basis = candidate.base(X) * sigma_geom
        numer += target * basis
        denom += basis * basis
    return 0.0 if denom == 0.0 else numer / denom


def main() -> None:
    parser = argparse.ArgumentParser(description="Short explicit envelope sweep for SS_formula.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument(
        "--candidate-list",
        type=str,
        default="log_x_plus_h_inv2,log_x_inv2,log_x_plus_half_h_inv2,x_neg_one_sixth",
    )
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    candidate_names = {name.strip() for name in args.candidate_list.split(",") if name.strip()}
    candidates = [c for c in CANDIDATES if c.name in candidate_names]
    if not candidates:
        raise SystemExit("empty candidate list")

    spf = smallest_prime_factors(max(Xs) + H)

    per_x = {}
    fit_rows: list[tuple[int, float, float]] = []

    for X in Xs:
        sparse_window = canonical_window_points(X)
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

        route_exact = [sl.raw0 + sl.nonzero_sum for sl in prime_slices]
        zero_exact = [sl.raw0 for sl in prime_slices]
        mean_exact = [sl.nonzero_sum for sl in prime_slices]
        geom_zero = [sl.raw0 for sl in geom_slices]
        geom_mean = [sl.nonzero_sum for sl in geom_slices]
        scale = [q0_norm_factor(N) for N in sparse_window]
        sigma = [singular_series_shape(N, spf) for N in sparse_window]

        G = [s * gm for s, gm in zip(scale, geom_mean)]
        zero_basis = [s * g0 * sig for s, g0, sig in zip(scale, geom_zero, sigma)]

        for z, basis in zip(zero_exact, zero_basis):
            fit_rows.append((X, z, basis))

        per_x[X] = {
            "route_exact": route_exact,
            "zero_exact": zero_exact,
            "mean_exact": mean_exact,
            "G": G,
            "zero_basis": zero_basis,
            "budget": normalized_route_budget(X),
        }

    for candidate in candidates:
        kappa = fit_global_kappa(candidate, fit_rows)
        residual_ratio_rows: list[tuple[int, float]] = []
        zero_ratio_rows: list[tuple[int, float]] = []

        print(f"== Candidate: {candidate.label} ==")
        print(f"kappa = {kappa:.12e}")
        print()

        for X in Xs:
            row = per_x[X]
            route_exact = row["route_exact"]
            zero_exact = row["zero_exact"]
            G = row["G"]
            budget = row["budget"]
            env = kappa * candidate.base(X)
            SS = [env * b for b in row["zero_basis"]]
            R = [rv - g - ss for rv, g, ss in zip(route_exact, G, SS)]

            zero_energy = dot([z - ss for z, ss in zip(zero_exact, SS)], [z - ss for z, ss in zip(zero_exact, SS)])
            residual_energy = dot(R, R)
            zero_ratio = zero_energy / budget
            residual_ratio = residual_energy / budget
            zero_ratio_rows.append((X, zero_ratio))
            residual_ratio_rows.append((X, residual_ratio))

            print(
                f"X={X:,}: env={env:.12e} "
                f"zero/budget={zero_ratio:.12e} residual/budget={residual_ratio:.12e}"
            )

        xs = [x for x, _ in zero_ratio_rows]
        zero_vals = [y for _, y in zero_ratio_rows]
        residual_vals = [y for _, y in residual_ratio_rows]
        print()
        print(f"zero-vs-SS exponent      = {fit_loglog_exponent(xs, zero_vals):.6f}")
        print(f"residual/budget exponent = {fit_loglog_exponent(xs, residual_vals):.6f}")
        print(f"max residual/budget      = {max(residual_vals):.12e}")
        print()


if __name__ == "__main__":
    main()
