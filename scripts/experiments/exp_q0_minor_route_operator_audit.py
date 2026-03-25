#!/usr/bin/env python3
"""
Exact route-operator audit for the minor family decomposition.

This script traces the actual route-facing quantity on the exact repo object:

  N ↦ Σ_t coeff(X,N,t)

and decomposes the weighted family into:

  weighted = coeffArith + α(X,N) * weightCentered + meanChannel

where:
  - coeffArith is the weight-regressed centered residual,
  - weightCentered is the centered weight-only sequence,
  - meanChannel is the constant-in-t centered correction plus the zero mode.

The goal is to make explicit where the route-facing mass actually lives.
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
    coeffarith_alpha,
    ensure_weights,
    mobius_phi_sieve,
    object_slice_vector,
    object_support,
    sum_by_s,
    weight_stats,
)


@dataclass
class ChannelReport:
    label: str
    slice_sums: list[float]
    energy: float

    @property
    def l2_norm(self) -> float:
        return math.sqrt(self.energy)


def energy_of_sums(sums: list[float]) -> float:
    return math.fsum(x * x for x in sums)


def channel_report(label: str, sums: list[float]) -> ChannelReport:
    return ChannelReport(label=label, slice_sums=sums, energy=energy_of_sums(sums))


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit the actual route-facing operator on the exact minor family decomposition.")
    parser.add_argument("--X", type=int, required=True)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--window", choices=["five", "three"], default="five")
    args = parser.parse_args()

    X = args.X
    window = canonical_window_points(X) if args.window == "five" else [X, X + H // 2, X + H]

    print("== Parameters ==")
    print(f"X={X:,} jobs={args.jobs} window={window}")

    print("[build] exact prime sum core")
    by_s = sum_by_s(X)
    print(f"[build] distinct sum levels: {len(by_s):,}")

    mu_q0, phi_q0 = mobius_phi_sieve(Q0)
    backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
    weights = ensure_weights(
        required_abs_t=range(0, X + H + 1),
        backend=backend,
        jobs=max(1, args.jobs),
        cache_file=cache_path(X, "exact", None),
    )

    slices = build_weighted_slices(X, window, weights, by_s)
    wstats = weight_stats(X, weights)

    ambient_support = object_support(X, slices, "coeffarith")
    weight_centered_vec = [weights[abs(t)] - wstats.mean_nonzero for t in ambient_support]
    weight_centered_sum = math.fsum(weight_centered_vec)
    weight_centered_energy = math.fsum(x * x for x in weight_centered_vec)

    weighted_sums: list[float] = []
    weighted_nonzero_sums: list[float] = []
    zero_mode_sums: list[float] = []
    centered_sums: list[float] = []
    coeffarith_sums: list[float] = []
    weight_channel_sums: list[float] = []
    mean_channel_sums: list[float] = []
    reconstruction_errors: list[float] = []

    for sl in slices:
        weighted_support = object_support(X, [sl], "weighted")
        weighted_vec = object_slice_vector(
            obj="weighted",
            support=weighted_support,
            sl=sl,
            weights=weights,
            wstats=None,
            alpha=None,
        )
        weighted_nonzero_vec = [sl.raw_nonzero.get(t, 0.0) for t in ambient_support]
        centered_vec = object_slice_vector(
            obj="centered",
            support=ambient_support,
            sl=sl,
            weights=weights,
            wstats=None,
            alpha=None,
        )
        alpha = coeffarith_alpha(sl, wstats, weights)
        coeffarith_vec = object_slice_vector(
            obj="coeffarith",
            support=ambient_support,
            sl=sl,
            weights=weights,
            wstats=wstats,
            alpha=alpha,
        )
        weight_channel_vec = [alpha * x for x in weight_centered_vec]
        mean_channel_vec = [sl.mean_nonzero for _ in ambient_support]

        weighted_sums.append(math.fsum(weighted_vec))
        weighted_nonzero_sums.append(math.fsum(weighted_nonzero_vec))
        zero_mode_sums.append(sl.raw0)
        centered_sums.append(math.fsum(centered_vec))
        coeffarith_sums.append(math.fsum(coeffarith_vec))
        weight_channel_sums.append(math.fsum(weight_channel_vec))
        mean_channel_sums.append(math.fsum(mean_channel_vec))

        # centered = coeffarith + alpha*weightCentered
        centered_recon = [a + b for a, b in zip(coeffarith_vec, weight_channel_vec)]
        centered_err = max(abs(a - b) for a, b in zip(centered_vec, centered_recon))

        # weighted nonzero part = centered + mean
        weighted_recon = [a + b for a, b in zip(centered_vec, mean_channel_vec)]
        weighted_err = max(abs(a - b) for a, b in zip(weighted_nonzero_vec, weighted_recon))

        reconstruction_errors.append(max(centered_err, weighted_err))

    reports = [
        channel_report("weighted family slice-sum", weighted_sums),
        channel_report("weighted nonzero slice-sum", weighted_nonzero_sums),
        channel_report("zero mode slice-sum", zero_mode_sums),
        channel_report("centered family slice-sum", centered_sums),
        channel_report("coeffArith slice-sum", coeffarith_sums),
        channel_report("weight channel α·w_centered slice-sum", weight_channel_sums),
        channel_report("mean channel slice-sum", mean_channel_sums),
    ]

    print("\n== Ambient Facts ==")
    print(f"ambient nonzero support size = {len(ambient_support):,}")
    print(f"weightCentered sum          = {weight_centered_sum:.12e}")
    print(f"weightCentered energy       = {weight_centered_energy:.12e}")
    print(f"max reconstruction error    = {max(reconstruction_errors):.12e}")

    print("\n== Route-Operator Channel Audit ==")
    for rep in reports:
        print(f"-- {rep.label} --")
        print("slice sums =", [f"{x:.12e}" for x in rep.slice_sums])
        print(f"energy     = {rep.energy:.12e}")
        print(f"l2 norm    = {rep.l2_norm:.12e}")

    print("\n== Identities ==")
    weighted_nonzero_vs_split = [
        a - (b + c)
        for a, b, c in zip(weighted_nonzero_sums, centered_sums, mean_channel_sums)
    ]
    weighted_vs_split = [
        a - (b + c + d)
        for a, b, c, d in zip(weighted_sums, zero_mode_sums, centered_sums, mean_channel_sums)
    ]
    centered_vs_split = [
        a - (b + c)
        for a, b, c in zip(weighted_sums, centered_sums, mean_channel_sums)
    ]
    coeff_vs_split = [
        a - (b + c)
        for a, b, c in zip(centered_sums, coeffarith_sums, weight_channel_sums)
    ]
    print("weighted nonzero - (centered + mean) =", [f"{x:.12e}" for x in weighted_nonzero_vs_split])
    print("weighted total - (zero + centered + mean) =", [f"{x:.12e}" for x in weighted_vs_split])
    print("weighted total - (zero + coeffArith + αw + mean) =", [f'{x:.12e}' for x in [a - (b + c + d + e) for a,b,c,d,e in zip(weighted_sums, zero_mode_sums, coeffarith_sums, weight_channel_sums, mean_channel_sums)]])
    print("centered - (coeffArith + αw) =", [f"{x:.12e}" for x in coeff_vs_split])


if __name__ == "__main__":
    main()
