#!/usr/bin/env python3
"""
Geometric-surrogate diagnostic on the route-visible minor object.

This is the conservative follow-up to the old coeffArith/subspace work.
Instead of studying the mean-zero residual sector directly, this script studies
the actual route-visible channels:

  zeroMode
  meanChannel
  routeVisible = zeroMode + meanChannel

The geometric surrogate is built from the same interval-convolution core used in
the earlier shadow audit, but the measurements are now taken on the route-visible
object itself.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

from exp_q0_minor_singularity_exact_harness import (
    H,
    Q0,
    SliceData,
    WeightBackend,
    build_weighted_slices,
    cache_path,
    canonical_window_points,
    ensure_weights,
    mobius_phi_sieve,
    sum_by_s,
)


UCUT = H + (H + 99) // 100


def k_full(k: int) -> float:
    if abs(k) > H:
        return 0.0
    return max(1.0 - abs(k) / float(UCUT), 0.0) / float(UCUT)


def sum_by_s_uniform_fast(X: int) -> dict[int, float]:
    lo = X // 2 - H
    hi = X // 2 + H
    s_lo = 2 * lo
    s_hi = 2 * hi

    even = [0.0]
    odd = [0.0]
    acc_even = 0.0
    acc_odd = 0.0
    for d in range(0, H + 1):
        val = k_full(d)
        if d % 2 == 0:
            acc_even += val
            even.append(acc_even)
        else:
            acc_odd += val
            odd.append(acc_odd)

    def parity_sum(M: int, parity: int) -> float:
        if M < 0:
            return 0.0
        if parity == 0:
            return even[M // 2 + 1]
        return odd[(M + 1) // 2]

    out: dict[int, float] = {}
    k0 = k_full(0)
    for s in range(s_lo, s_hi + 1):
        M = min(H, s - s_lo, s_hi - s)
        parity = s & 1
        total = k0 if parity == 0 else 0.0
        if M >= (2 if parity == 0 else 1):
            total += 2.0 * parity_sum(M, parity)
            if parity == 0:
                total -= 2.0 * k0
        out[s] = total
    return out


def parse_x_list(spec: str) -> list[int]:
    out: list[int] = []
    for piece in spec.split(","):
        piece = piece.strip()
        if piece:
            out.append(int(piece))
    if not out:
        raise SystemExit("empty --X-list")
    return out


def dot(u: list[float], v: list[float]) -> float:
    return math.fsum(a * b for a, b in zip(u, v))


def fit_scalar(actual: list[float], model: list[float]) -> tuple[float, float, float]:
    denom = dot(model, model)
    if denom == 0.0:
        beta = 0.0
    else:
        beta = dot(actual, model) / denom
    residual = [a - beta * m for a, m in zip(actual, model)]
    full_energy = dot(actual, actual)
    residual_energy = dot(residual, residual)
    captured_energy = max(full_energy - residual_energy, 0.0)
    return beta, captured_energy, residual_energy


def fit_weighted_scalar(actual: list[float], model: list[float], weight: float) -> tuple[float, float, float]:
    weighted_actual = [math.sqrt(weight) * x for x in actual]
    weighted_model = [math.sqrt(weight) * x for x in model]
    return fit_scalar(weighted_actual, weighted_model)


def fit_loglog_exponent(xs: list[int], ys: list[float]) -> float:
    lx = [math.log(float(x)) for x in xs]
    ly = [math.log(float(y)) for y in ys]
    mx = sum(lx) / len(lx)
    my = sum(ly) / len(ly)
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    den = sum((a - mx) * (a - mx) for a in lx)
    return num / den


@dataclass
class ObservableData:
    zero: list[float]
    mean_coeff: list[float]
    mean_sum: list[float]
    route_sum: list[float]


@dataclass
class FitReport:
    beta: float
    captured_energy: float
    residual_energy: float

    @property
    def capture_ratio(self) -> float:
        total = self.captured_energy + self.residual_energy
        return 0.0 if total == 0.0 else self.captured_energy / total


def observable_data(X: int, slices: list[SliceData]) -> tuple[ObservableData, int]:
    ambient_nonzero_size = 2 * (X + H)
    zero = [sl.raw0 for sl in slices]
    mean_coeff = [sl.mean_nonzero for sl in slices]
    mean_sum = [sl.nonzero_sum for sl in slices]
    route_sum = [sl.raw0 + sl.nonzero_sum for sl in slices]
    return ObservableData(zero=zero, mean_coeff=mean_coeff, mean_sum=mean_sum, route_sum=route_sum), ambient_nonzero_size


def main() -> None:
    parser = argparse.ArgumentParser(description="Geometric surrogate study on zeroMode + meanChannel.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)

    route_norm_rows: list[tuple[int, float]] = []
    route_residual_rows: list[tuple[int, float]] = []
    family_residual_rows: list[tuple[int, float]] = []

    for X in Xs:
        window = canonical_window_points(X)

        print(f"== X={X:,} ==")
        print("[build] exact prime core")
        prime_by_s = sum_by_s(X)
        print(f"[build] prime sum levels: {len(prime_by_s):,}")

        print("[build] geometric surrogate core")
        geom_by_s = sum_by_s_uniform_fast(X)
        print(f"[build] surrogate sum levels: {len(geom_by_s):,}")

        mu_q0, phi_q0 = mobius_phi_sieve(Q0)
        backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
        weights = ensure_weights(
            required_abs_t=range(0, X + 2 * H + 1),
            backend=backend,
            jobs=max(1, args.jobs),
            cache_file=cache_path(X, "exact", None),
        )

        prime_slices = build_weighted_slices(X, window, weights, prime_by_s)
        geom_slices = build_weighted_slices(X, window, weights, geom_by_s)

        prime_obs, ambient_size = observable_data(X, prime_slices)
        geom_obs, _ = observable_data(X, geom_slices)

        zero_fit = FitReport(*fit_scalar(prime_obs.zero, geom_obs.zero))
        mean_coeff_fit = FitReport(*fit_weighted_scalar(prime_obs.mean_coeff, geom_obs.mean_coeff, float(ambient_size)))
        mean_sum_fit = FitReport(*fit_scalar(prime_obs.mean_sum, geom_obs.mean_sum))
        route_sum_fit = FitReport(*fit_scalar(prime_obs.route_sum, geom_obs.route_sum))

        route_family_energy = dot(prime_obs.zero, prime_obs.zero) + ambient_size * dot(prime_obs.mean_coeff, prime_obs.mean_coeff)
        route_family_residual = zero_fit.residual_energy + mean_coeff_fit.residual_energy
        route_family_capture = max(route_family_energy - route_family_residual, 0.0)

        route_norm = math.sqrt(dot(prime_obs.route_sum, prime_obs.route_sum))
        route_residual_norm = math.sqrt(route_sum_fit.residual_energy)
        family_residual_norm = math.sqrt(route_family_residual)

        route_norm_rows.append((X, route_norm))
        route_residual_rows.append((X, route_residual_norm))
        family_residual_rows.append((X, family_residual_norm))

        print(f"window={window}")
        print(f"ambient_nonzero_size={ambient_size:,}")
        print()
        print("-- route-facing norms --")
        print(f"zeroMode norm                 = {math.sqrt(dot(prime_obs.zero, prime_obs.zero)):.12e}")
        print(f"meanChannel sum norm          = {math.sqrt(dot(prime_obs.mean_sum, prime_obs.mean_sum)):.12e}")
        print(f"routeVisible scalar norm      = {route_norm:.12e}")
        print(f"routeVisible family norm      = {math.sqrt(route_family_energy):.12e}")
        print()
        print("-- geometric surrogate fits --")
        print(
            f"zeroMode:      beta={zero_fit.beta:.12e} "
            f"capture={100.0 * zero_fit.capture_ratio:.6f}% "
            f"residual_norm={math.sqrt(zero_fit.residual_energy):.12e}"
        )
        print(
            f"meanChannel:   beta={mean_coeff_fit.beta:.12e} "
            f"capture={100.0 * mean_coeff_fit.capture_ratio:.6f}% "
            f"residual_norm={math.sqrt(mean_coeff_fit.residual_energy):.12e} "
            f"(weighted by ambient size)"
        )
        print(
            f"mean sum:      beta={mean_sum_fit.beta:.12e} "
            f"capture={100.0 * mean_sum_fit.capture_ratio:.6f}% "
            f"residual_norm={math.sqrt(mean_sum_fit.residual_energy):.12e}"
        )
        print(
            f"route scalar:  beta={route_sum_fit.beta:.12e} "
            f"capture={100.0 * route_sum_fit.capture_ratio:.6f}% "
            f"residual_norm={route_residual_norm:.12e}"
        )
        family_capture_ratio = 0.0 if route_family_energy == 0.0 else route_family_capture / route_family_energy
        print(
            f"route family:  capture={100.0 * family_capture_ratio:.6f}% "
            f"residual_norm={family_residual_norm:.12e}"
        )
        print()

    if len(Xs) >= 2:
        xs = [x for x, _ in route_norm_rows]
        route_norms = [y for _, y in route_norm_rows]
        route_residuals = [y for _, y in route_residual_rows]
        family_residuals = [y for _, y in family_residual_rows]
        print("== Log-Log Exponents ==")
        print(f"routeVisible scalar norm exponent        = {fit_loglog_exponent(xs, route_norms):.6f}")
        print(f"routeVisible scalar residual exponent    = {fit_loglog_exponent(xs, route_residuals):.6f}")
        print(f"routeVisible family residual exponent    = {fit_loglog_exponent(xs, family_residuals):.6f}")


if __name__ == "__main__":
    main()
