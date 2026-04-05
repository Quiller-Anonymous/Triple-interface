#!/usr/bin/env python3
"""
Bookkeeping-toggle provenance diagnostic for the remaining zero-mode scalar.

Starting from the stabilized observable

  zero / (q0 * geom0 * sigma * c_X),

this script applies a short fixed list of convention toggles and reports the resulting constants.

The goal is not to refit anything, but to see whether the remaining scalar is plausibly explained
by one leftover mass/symmetry convention:

- mean vs sum over the dense even window,
- even-window vs full-window count,
- symmetry factor 2,
- endpoint half-weight factor.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import H, Q0, WeightBackend, mobius_phi_sieve, q0_norm_factor, sum_by_s
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


def nearest_unit_fraction(x: float, max_den: int = 2000) -> tuple[int, float]:
    best_d = 1
    best_err = abs(x - 1.0)
    for d in range(1, max_den + 1):
        err = abs(x - 1.0 / d)
        if err < best_err:
            best_d = d
            best_err = err
    return best_d, best_err


def stabilized_constant(X: int, step: int, spf: list[int]) -> tuple[float, int, int]:
    Ns = even_window(X, step)
    prime_by_s = sum_by_s(X)
    geom_by_s = sum_by_s_uniform_fast(X)
    cX = route_window_floor(X)

    mu_q0, phi_q0 = mobius_phi_sieve(Q0)
    backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
    w0 = backend.minor_weight(0)

    vals: list[float] = []
    for N in Ns:
        zero = q0_norm_factor(N) * prime_by_s.get(N, 0.0) * w0
        geom0 = q0_norm_factor(N) * geom_by_s.get(N, 0.0) * w0
        sigma = singular_series_shape(N, spf)
        if abs(geom0) <= 1e-30 or abs(sigma) <= 1e-30 or abs(cX) <= 1e-30:
            continue
        vals.append(zero / (geom0 * sigma * cX))
    return mean(vals), len(Ns), H + 1


def main() -> None:
    parser = argparse.ArgumentParser(description="Zero-mode bookkeeping constant toggles.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)

    for X in Xs:
        base, even_count, full_count = stabilized_constant(X, args.step, spf)
        endpoint_half_factor = (even_count - 1) / even_count
        even_to_full = full_count / even_count
        toggles = {
            "raw": base,
            "times even_count": base * even_count,
            "times full_count": base * full_count,
            "times full/even": base * even_to_full,
            "times symmetry_2": base * 2.0,
            "times half_sym": base * 0.5,
            "times endpoint_half": base * endpoint_half_factor,
            "times symmetry_2*endpoint_half": base * 2.0 * endpoint_half_factor,
        }

        print(f"== X={X:,} ==")
        print(f"base stabilized constant = {base:.12e}")
        print(f"even_count={even_count} full_count={full_count} full/even={even_to_full:.12e}")
        print()
        for label, value in toggles.items():
            d, err = nearest_unit_fraction(value)
            print(
                f"{label:30s} value={value:.12e}  nearest 1/{d}={1.0/d:.12e}  err={err:.12e}"
            )
        print()


if __name__ == "__main__":
    main()
