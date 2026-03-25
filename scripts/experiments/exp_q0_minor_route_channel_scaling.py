#!/usr/bin/env python3
"""
Per-channel scaling study for the exact route-facing minor decomposition.

This script measures, across a list of X-scales, the route-facing slice-sum
`ℓ²_N` norm carried by each exact channel in the weighted minor family:

  weighted total
  weighted nonzero
  zero mode
  centered
  coeffArith
  weight channel
  mean channel

The purpose is to identify where the growth actually lives before any new
minor bridge architecture is built.
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
class ChannelStats:
    sums: list[float]

    @property
    def energy(self) -> float:
        return math.fsum(x * x for x in self.sums)

    @property
    def norm(self) -> float:
        return math.sqrt(self.energy)


def parse_x_list(spec: str) -> list[int]:
    out: list[int] = []
    for piece in spec.split(","):
        piece = piece.strip().lower()
        if not piece:
            continue
        if piece.endswith("e4"):
            out.append(int(float(piece)))
        elif piece.endswith("e5"):
            out.append(int(float(piece)))
        elif piece.endswith("e6"):
            out.append(int(float(piece)))
        else:
            out.append(int(piece))
    if not out:
        raise SystemExit("empty --X-list")
    return out


def fit_loglog_exponent(xs: list[int], ys: list[float]) -> float:
    lx = [math.log(float(x)) for x in xs]
    ly = [math.log(float(y)) for y in ys]
    mx = sum(lx) / len(lx)
    my = sum(ly) / len(ly)
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    den = sum((a - mx) * (a - mx) for a in lx)
    return num / den


def main() -> None:
    parser = argparse.ArgumentParser(description="Exact per-channel route-facing scaling study.")
    parser.add_argument("--X-list", type=str, default="10000,30000,100000,300000,1000000")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--window", choices=["five", "three"], default="five")
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)

    all_stats: dict[str, list[tuple[int, float, float]]] = {
        "weighted_total": [],
        "weighted_nonzero": [],
        "zero_mode": [],
        "centered": [],
        "coeffarith": [],
        "weight_channel": [],
        "mean_channel": [],
    }

    for X in Xs:
        window = canonical_window_points(X) if args.window == "five" else [X, X + H // 2, X + H]
        print(f"== X={X:,} ==")
        by_s = sum_by_s(X)
        print(f"[build] sum levels: {len(by_s):,}")

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

        weighted_total_sums: list[float] = []
        weighted_nonzero_sums: list[float] = []
        zero_mode_sums: list[float] = []
        centered_sums: list[float] = []
        coeffarith_sums: list[float] = []
        weight_channel_sums: list[float] = []
        mean_channel_sums: list[float] = []

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
            weighted_nonzero_vec = [sl.raw_nonzero.get(t, 0.0) for t in ambient_support]

            weighted_total_sums.append(math.fsum(weighted_vec))
            weighted_nonzero_sums.append(math.fsum(weighted_nonzero_vec))
            zero_mode_sums.append(sl.raw0)
            centered_sums.append(math.fsum(centered_vec))
            coeffarith_sums.append(math.fsum(coeffarith_vec))
            weight_channel_sums.append(math.fsum(weight_channel_vec))
            mean_channel_sums.append(math.fsum(mean_channel_vec))

        channel_data = {
            "weighted_total": ChannelStats(weighted_total_sums),
            "weighted_nonzero": ChannelStats(weighted_nonzero_sums),
            "zero_mode": ChannelStats(zero_mode_sums),
            "centered": ChannelStats(centered_sums),
            "coeffarith": ChannelStats(coeffarith_sums),
            "weight_channel": ChannelStats(weight_channel_sums),
            "mean_channel": ChannelStats(mean_channel_sums),
        }

        for label, stats in channel_data.items():
            all_stats[label].append((X, stats.energy, stats.norm))
            print(f"{label:16s} energy={stats.energy:.12e} norm={stats.norm:.12e}")
        print()

    print("== Log-Log Exponents ==")
    for label, rows in all_stats.items():
        xs = [x for x, _, _ in rows]
        energies = [e for _, e, _ in rows]
        norms = [n for _, _, n in rows]
        e_exp = fit_loglog_exponent(xs, energies)
        n_exp = fit_loglog_exponent(xs, norms)
        print(f"{label:16s} energy_exponent={e_exp:.6f} norm_exponent={n_exp:.6f}")


if __name__ == "__main__":
    main()
