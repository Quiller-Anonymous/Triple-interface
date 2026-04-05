#!/usr/bin/env python3
"""
Upstream provenance diagnostic for the remaining zero-mode bookkeeping scalar.

This script tests three upstream suspects directly:

1. `q0NormFactor` / exact `t = 0` Fourier weight cancellation,
2. geometric zero-baseline total mass,
3. zero-mode support/symmetry choices in the geometric baseline.

The main quantity is the stabilized constant after dividing by:

  q0NormFactor(N) * geometric baseline * sigma(N) * c_X.

We compare that constant under several explicit upstream baseline variants.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import H, Q0, WeightBackend, k_full_on_sbg, mobius_phi_sieve, q0_norm_factor, sum_by_s
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


def route_window_floor(X: int) -> float:
    return (1.0 / 800.0) * (1.0 / (math.log(X + H) ** 2))


def mean(xs: list[float]) -> float:
    return sum(xs) / len(xs)


def variance(xs: list[float]) -> float:
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs) / len(xs)


def summarize(label: str, vals: list[float]) -> None:
    m = mean(vals)
    std = math.sqrt(variance(vals))
    cv = 0.0 if abs(m) <= 1e-30 else std / abs(m)
    print(f"{label:24s} mean={m:.12e}  std={std:.12e}  cv={cv:.12e}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Zero-mode upstream factor diagnostic.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)
    k0 = k_full_on_sbg(0)

    for X in Xs:
        Ns = even_window(X, args.step)
        cX = route_window_floor(X)
        prime_by_s = sum_by_s(X)
        geom_by_s = sum_by_s_uniform_fast(X)

        mu_q0, phi_q0 = mobius_phi_sieve(Q0)
        backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
        w0 = backend.minor_weight(0)

        with_q0_w0: list[float] = []
        cancel_q0_only: list[float] = []
        cancel_q0_w0: list[float] = []
        geom_half: list[float] = []
        geom_offdiag: list[float] = []
        geom_offdiag_half: list[float] = []

        for N in Ns:
            zero = q0_norm_factor(N) * prime_by_s.get(N, 0.0) * w0
            geom_full = q0_norm_factor(N) * geom_by_s.get(N, 0.0) * w0
            sigma = singular_series_shape(N, spf)
            if abs(sigma) <= 1e-30 or abs(cX) <= 1e-30:
                continue

            s = N
            geom_mass = geom_by_s.get(s, 0.0)
            geom_mass_half = 0.5 * geom_mass
            geom_mass_offdiag = geom_mass - k0
            geom_mass_offdiag_half = 0.5 * geom_mass_offdiag

            if abs(geom_full) > 1e-30:
                with_q0_w0.append(zero / (geom_full * sigma * cX))
            if abs(q0_norm_factor(N) * geom_mass * w0) > 1e-30:
                cancel_q0_only.append(
                    zero / ((q0_norm_factor(N) * geom_mass * w0) * sigma * cX)
                )
            if abs(geom_mass * sigma * cX) > 1e-30:
                cancel_q0_w0.append(
                    prime_by_s.get(s, 0.0) / (geom_mass * sigma * cX)
                )
            if abs(geom_mass_half * sigma * cX) > 1e-30:
                geom_half.append(
                    prime_by_s.get(s, 0.0) / (geom_mass_half * sigma * cX)
                )
            if abs(geom_mass_offdiag * sigma * cX) > 1e-30:
                geom_offdiag.append(
                    prime_by_s.get(s, 0.0) / (geom_mass_offdiag * sigma * cX)
                )
            if abs(geom_mass_offdiag_half * sigma * cX) > 1e-30:
                geom_offdiag_half.append(
                    prime_by_s.get(s, 0.0) / (geom_mass_offdiag_half * sigma * cX)
                )

        print(f"== X={X:,} ==")
        print(f"w0={w0:.12e}  k0={k0:.12e}")
        print()
        summarize("full observable", with_q0_w0)
        summarize("cancel q0 only", cancel_q0_only)
        summarize("cancel q0 and w0", cancel_q0_w0)
        summarize("geom half-mass", geom_half)
        summarize("geom offdiag only", geom_offdiag)
        summarize("geom offdiag half", geom_offdiag_half)
        print()


if __name__ == "__main__":
    main()
