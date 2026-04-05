#!/usr/bin/env python3
"""
Compare the fitted zero-mode envelope E(X) against normalization-scale candidates.

This is a provenance diagnostic for the promoted fixed witness

  sigmaEnvelopeFormula(X) = kappa / log(X + H)^2.

The goal is not to refit the witness, but to check whether the empirically extracted envelope
tracks the same `log(X + H)^(-2)` seam already present in the route normalization floor `c_X`.
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


def route_window_floor_alt_logX(X: int) -> float:
    return (1.0 / 800.0) * (1.0 / (math.log(X) ** 2))


def candidate_rows(X: int) -> dict[str, float]:
    return {
        "c_X(log(X+H))": route_window_floor(X),
        "c_X(log(X))": route_window_floor_alt_logX(X),
        "log(X+H)^-2": 1.0 / (math.log(X + H) ** 2),
        "log(X)^-2": 1.0 / (math.log(X) ** 2),
        "X^(-1/6)": X ** (-1.0 / 6.0),
    }


def fitted_zero_envelope(X: int, step: int, spf: list[int]) -> float:
    Ns = even_window(X, step)
    prime_by_s = sum_by_s(X)
    geom_by_s = sum_by_s_uniform_fast(X)

    mu_q0, phi_q0 = mobius_phi_sieve(Q0)
    backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
    w0 = backend.minor_weight(0)

    z_vals: list[float] = []
    sigma_vals: list[float] = []

    for N in Ns:
        zero_exact = q0_norm_factor(N) * prime_by_s.get(N, 0.0) * w0
        geom0 = q0_norm_factor(N) * geom_by_s.get(N, 0.0) * w0
        sigma = singular_series_shape(N, spf)
        if abs(geom0) <= 1e-30 or abs(sigma) <= 1e-30:
            continue
        z_vals.append(zero_exact / geom0)
        sigma_vals.append(sigma)

    sigma_dot_sigma = sum(s * s for s in sigma_vals)
    if sigma_dot_sigma == 0.0:
        return 0.0
    return sum(z * s for z, s in zip(z_vals, sigma_vals)) / sigma_dot_sigma


def main() -> None:
    parser = argparse.ArgumentParser(description="Zero-mode envelope provenance diagnostic.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    envelope_rows: list[tuple[int, float]] = []

    for X in Xs:
        e_fit = fitted_zero_envelope(X, args.step, spf)
        envelope_rows.append((X, e_fit))
        candidates = candidate_rows(X)

        print(f"== X={X:,} ==")
        print(f"fitted envelope E(X) = {e_fit:.12e}")
        print()
        print("-- normalization-scale comparisons --")
        for label, value in candidates.items():
            ratio = 0.0 if abs(value) <= 1e-30 else e_fit / value
            print(f"{label:20s} value={value:.12e}  E/value={ratio:.12e}")
        print()

    if len(envelope_rows) >= 2:
        xs = [x for x, _ in envelope_rows]
        es = [e for _, e in envelope_rows]
        print("== Log-Log Exponents ==")
        print(f"E(X) exponent               = {fit_loglog_exponent(xs, es):.6f}")
        print(f"E(X) / c_X(log(X+H))       exponent = {fit_loglog_exponent(xs, [e / route_window_floor(x) for x, e in envelope_rows]):.6f}")
        print(f"E(X) / log(X+H)^-2         exponent = {fit_loglog_exponent(xs, [e / (1.0 / (math.log(x + H) ** 2)) for x, e in envelope_rows]):.6f}")


if __name__ == "__main__":
    main()
