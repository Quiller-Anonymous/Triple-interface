#!/usr/bin/env python3
"""
Residual low-rank diagnostic for the route-visible minor family.

This is the follow-up to `exp_q0_minor_route_visible_surrogate.py`.
It studies the actual route-visible family

  routeVisible = zeroMode + meanChannel

after subtracting the best geometric surrogate fit channel-by-channel.

The goal is not to make the residual the new bridge. The goal is to answer:

1. After removing the geometric main term, is the remaining route-visible family
   low-rank across the sampled centers N?
2. Does that residual still carry substantial route-facing mass?
3. Is the residual materially simpler than the raw route-visible family?
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import (
    H,
    Q0,
    BasisData,
    WeightBackend,
    basis_projection,
    basis_report,
    build_family_vectors,
    build_weighted_slices,
    cache_path,
    canonical_window_points,
    dot,
    ensure_weights,
    mobius_phi_sieve,
    sum_by_s,
    svd_basis_from_family_vectors,
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


def fit_scalar(actual: list[float], model: list[float]) -> float:
    denom = dot(model, model)
    if denom == 0.0:
        return 0.0
    return dot(actual, model) / denom


def parse_rank_list(spec: str) -> list[int]:
    out: list[int] = []
    for piece in spec.split(","):
        piece = piece.strip()
        if piece:
            out.append(int(piece))
    if not out:
        raise SystemExit("empty --rank-list")
    return out


def residual_vectors_from_channel_fit(
    *,
    support: list[int],
    prime_vectors: list[list[float]],
    geom_vectors: list[list[float]],
    beta_zero: float,
    beta_mean: float,
) -> list[list[float]]:
    zero_idx = support.index(0)
    residual: list[list[float]] = []
    for prime_vec, geom_vec in zip(prime_vectors, geom_vectors):
        cur = prime_vec[:]
        cur[zero_idx] -= beta_zero * geom_vec[zero_idx]
        for i, t in enumerate(support):
            if t != 0:
                cur[i] -= beta_mean * geom_vec[i]
        residual.append(cur)
    return residual


def main() -> None:
    parser = argparse.ArgumentParser(description="Residual subspace diagnostic on zeroMode + meanChannel.")
    parser.add_argument("--X", type=int, required=True)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--rank-list", type=str, default="1,2,3")
    args = parser.parse_args()

    X = args.X
    ranks = parse_rank_list(args.rank_list)
    window = canonical_window_points(X)

    print("== Parameters ==")
    print(f"X={X:,} jobs={args.jobs} rank_list={ranks}")
    print(f"window={window}")

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

    support, prime_vectors = build_family_vectors(
        X=X,
        obj="routevisible",
        slices=prime_slices,
        weights=weights,
        wstats=None,
    )
    geom_support, geom_vectors = build_family_vectors(
        X=X,
        obj="routevisible",
        slices=geom_slices,
        weights=weights,
        wstats=None,
    )
    if geom_support != support:
        raise SystemExit("support mismatch between prime and geometric route-visible families")

    prime_zero = [sl.raw0 for sl in prime_slices]
    geom_zero = [sl.raw0 for sl in geom_slices]
    prime_mean = [sl.mean_nonzero for sl in prime_slices]
    geom_mean = [sl.mean_nonzero for sl in geom_slices]

    beta_zero = fit_scalar(prime_zero, geom_zero)
    beta_mean = fit_scalar(prime_mean, geom_mean)
    residual_vectors = residual_vectors_from_channel_fit(
        support=support,
        prime_vectors=prime_vectors,
        geom_vectors=geom_vectors,
        beta_zero=beta_zero,
        beta_mean=beta_mean,
    )

    route_basis, route_cumulative = svd_basis_from_family_vectors(
        support=support,
        vectors=prime_vectors,
        rank=max(ranks),
        label=f"routevisible-family-svd-X{X}-rank{max(ranks)}",
    )
    residual_basis, residual_cumulative = svd_basis_from_family_vectors(
        support=support,
        vectors=residual_vectors,
        rank=max(ranks),
        label=f"routevisible-residual-svd-X{X}-rank{max(ranks)}",
    )

    prime_report_full = basis_report(prime_vectors, BasisData(support=support, basis=[], orthonormal=True, label="zero"))
    residual_report_full = basis_report(residual_vectors, BasisData(support=support, basis=[], orthonormal=True, label="zero"))

    print()
    print("== Channel Fit ==")
    print(f"beta_zeroMode      = {beta_zero:.12e}")
    print(f"beta_meanChannel   = {beta_mean:.12e}")
    print(f"prime family norm  = {math.sqrt(prime_report_full.full_family_energy):.12e}")
    print(f"residual family norm = {math.sqrt(residual_report_full.full_family_energy):.12e}")
    ratio = 0.0 if prime_report_full.full_family_energy == 0.0 else residual_report_full.full_family_energy / prime_report_full.full_family_energy
    print(f"residual energy ratio = {100.0 * ratio:.6f}%")

    print()
    print("== SVD Capture ==")
    for rank in ranks:
        route_basis_k = BasisData(
            support=support,
            basis=route_basis.basis[:rank],
            orthonormal=True,
            label=f"routevisible-rank{rank}",
        )
        residual_basis_k = BasisData(
            support=support,
            basis=residual_basis.basis[:rank],
            orthonormal=True,
            label=f"routevisible-residual-rank{rank}",
        )
        route_report = basis_report(prime_vectors, route_basis_k)
        residual_report = basis_report(residual_vectors, residual_basis_k)
        print(
            f"route rank {rank}: "
            f"capture={100.0 * route_report.capture_ratio:.6f}% "
            f"shadowResidual={100.0 * route_report.shadow_residual_ratio:.6e}% "
            f"cumSVD={100.0 * route_cumulative[min(rank, len(route_cumulative)) - 1]:.6f}%"
        )
        print(
            f"resid rank {rank}: "
            f"capture={100.0 * residual_report.capture_ratio:.6f}% "
            f"shadowResidual={100.0 * residual_report.shadow_residual_ratio:.6e}% "
            f"cumSVD={100.0 * residual_cumulative[min(rank, len(residual_cumulative)) - 1]:.6f}%"
        )

    print()
    print("== Residual Slice Sums ==")
    for N, vec in zip(window, residual_vectors):
        print(f"N={N}: residual_sum={math.fsum(vec):.12e} residual_norm={math.sqrt(dot(vec, vec)):.12e}")

    print()
    print("== Residual Leading Coordinates ==")
    top_t = [0, 1, -1, 2, -2, H, -H]
    for t in top_t:
        if t not in support:
            continue
        idx = support.index(t)
        values = [vec[idx] for vec in residual_vectors]
        print(f"t={t}: " + " ".join(f"{x:.6e}" for x in values))


if __name__ == "__main__":
    main()
