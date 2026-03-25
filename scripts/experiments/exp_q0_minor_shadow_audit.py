#!/usr/bin/env python3
"""
Shadow-map audit for the exact coeffArith family.

This script is the next bridge-facing diagnostic layer on top of
`exp_q0_minor_singularity_exact_harness.py`.

It answers three questions on the exact repo object:

1. How does the route-facing shadow map act on the empirical family basis,
   the geometric surrogate basis, and the empirical complement basis?
2. Is the tiny shadow residual better explained by a near-kernel of the
   shadow operator, or by support geometry?
3. How much of the exact family is already captured by the geometric
   left-edge surrogate before the arithmetic refinement is added back in?
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from decimal import Decimal, getcontext

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
    gram_schmidt_orthonormalize,
    mobius_phi_sieve,
    sum_by_s,
    svd_basis_from_family_vectors,
    weight_stats,
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


def corr(u: list[float], v: list[float]) -> float:
    nu = math.sqrt(max(dot(u, u), 0.0))
    nv = math.sqrt(max(dot(v, v), 0.0))
    if nu <= 1e-18 or nv <= 1e-18:
        return 0.0
    return dot(u, v) / (nu * nv)


def basis_sums(basis: BasisData) -> list[float]:
    return [math.fsum(vec) for vec in basis.basis]


def basis_sums_decimal(basis: BasisData, prec: int) -> list[Decimal]:
    getcontext().prec = prec
    out: list[Decimal] = []
    for vec in basis.basis:
        out.append(sum(Decimal(repr(x)) for x in vec))
    return out


def operator_norm_from_basis_sums(sums: list[float]) -> float:
    return math.sqrt(sum(x * x for x in sums))


def operator_norm_from_basis_sums_decimal(sums: list[Decimal]) -> Decimal:
    acc = sum(x * x for x in sums)
    return acc.sqrt() if acc != 0 else Decimal(0)


def project_family(vectors: list[list[float]], basis: BasisData) -> tuple[list[list[float]], list[list[float]]]:
    approx_vectors: list[list[float]] = []
    residual_vectors: list[list[float]] = []
    for vec in vectors:
        approx, residual = basis_projection(vec, basis)
        approx_vectors.append(approx)
        residual_vectors.append(residual)
    return approx_vectors, residual_vectors


def orthonormal_basis_from_vectors(support: list[int], vectors: list[list[float]], label: str) -> BasisData:
    return BasisData(
        support=support,
        basis=gram_schmidt_orthonormalize(vectors),
        orthonormal=True,
        label=label,
    )


@dataclass
class SpaceAudit:
    label: str
    dimension: int
    basis_sums: list[float]
    operator_norm: float
    decimal_basis_sums: list[Decimal] | None = None
    decimal_operator_norm: Decimal | None = None


def audit_space(basis: BasisData, decimal_prec: int | None) -> SpaceAudit:
    sums = basis_sums(basis)
    dec_sums = None
    dec_norm = None
    if decimal_prec is not None:
        dec_sums = basis_sums_decimal(basis, decimal_prec)
        dec_norm = operator_norm_from_basis_sums_decimal(dec_sums)
    return SpaceAudit(
        label=basis.label or "basis",
        dimension=len(basis.basis),
        basis_sums=sums,
        operator_norm=operator_norm_from_basis_sums(sums),
        decimal_basis_sums=dec_sums,
        decimal_operator_norm=dec_norm,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit the exact shadow map on coeffArith and geometric surrogate spaces.")
    parser.add_argument("--X", type=int, required=True)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--empirical-rank", type=int, default=3)
    parser.add_argument("--geometric-rank", type=int, default=3)
    parser.add_argument("--complement-rank", type=int, default=3)
    parser.add_argument("--decimal-prec", type=int, default=80)
    args = parser.parse_args()

    X = args.X
    window = canonical_window_points(X)

    print("== Parameters ==")
    print(
        f"X={X:,} jobs={args.jobs} empirical_rank={args.empirical_rank} "
        f"geometric_rank={args.geometric_rank} complement_rank={args.complement_rank} "
        f"decimal_prec={args.decimal_prec}"
    )
    print(f"window={window}")

    print("[build] prime core")
    prime_by_s = sum_by_s(X)
    print(f"[build] prime sum levels: {len(prime_by_s):,}")

    print("[build] geometric surrogate core")
    geom_by_s = sum_by_s_uniform_fast(X)
    print(f"[build] surrogate sum levels: {len(geom_by_s):,}")

    mu_q0, phi_q0 = mobius_phi_sieve(Q0)
    backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
    weights = ensure_weights(
        required_abs_t=range(0, X + H + 1),
        backend=backend,
        jobs=max(1, args.jobs),
        cache_file=cache_path(X, "exact", None),
    )
    wstats = weight_stats(X, weights)

    prime_slices = build_weighted_slices(X, window, weights, prime_by_s)
    geom_slices = build_weighted_slices(X, window, weights, geom_by_s)

    support, prime_vectors = build_family_vectors(
        X=X,
        obj="coeffarith",
        slices=prime_slices,
        weights=weights,
        wstats=wstats,
    )
    geom_support, geom_vectors = build_family_vectors(
        X=X,
        obj="coeffarith",
        slices=geom_slices,
        weights=weights,
        wstats=wstats,
    )
    if geom_support != support:
        raise SystemExit("Support mismatch between exact and geometric coeffArith families.")

    empirical_basis, empirical_cumulative = svd_basis_from_family_vectors(
        support=support,
        vectors=prime_vectors,
        rank=args.empirical_rank,
        label=f"empirical-coeffarith-X{X}-rank{args.empirical_rank}",
    )
    geometric_basis, geometric_cumulative = svd_basis_from_family_vectors(
        support=support,
        vectors=geom_vectors,
        rank=args.geometric_rank,
        label=f"geometric-surrogate-X{X}-rank{args.geometric_rank}",
    )

    empirical_approx, empirical_residual = project_family(prime_vectors, empirical_basis)
    complement_basis, complement_cumulative = svd_basis_from_family_vectors(
        support=support,
        vectors=empirical_residual,
        rank=args.complement_rank,
        label=f"empirical-complement-X{X}-rank{args.complement_rank}",
    )

    empirical_report = basis_report(prime_vectors, empirical_basis)
    geometric_on_prime_report = basis_report(prime_vectors, geometric_basis)

    empirical_audit = audit_space(empirical_basis, args.decimal_prec)
    geometric_audit = audit_space(geometric_basis, args.decimal_prec)
    complement_audit = audit_space(complement_basis, args.decimal_prec)

    print("\n== Family Reports ==")
    print(
        f"empirical capture={100.0 * empirical_report.capture_ratio:.6f}% "
        f"residual={100.0 * empirical_report.residual_ratio:.6f}% "
        f"shadowResidual={100.0 * empirical_report.shadow_residual_ratio:.6e}%"
    )
    print(
        f"geometric-on-prime capture={100.0 * geometric_on_prime_report.capture_ratio:.6f}% "
        f"residual={100.0 * geometric_on_prime_report.residual_ratio:.6f}% "
        f"shadowResidual={100.0 * geometric_on_prime_report.shadow_residual_ratio:.6e}%"
    )

    print("\n== Cumulative Captures ==")
    print(
        "empirical: "
        + ", ".join(
            f"r={i+1}:{100.0 * empirical_cumulative[i]:.4f}%"
            for i in range(min(len(empirical_cumulative), len(prime_vectors)))
        )
    )
    print(
        "geometric: "
        + ", ".join(
            f"r={i+1}:{100.0 * geometric_cumulative[i]:.4f}%"
            for i in range(min(len(geometric_cumulative), len(geom_vectors)))
        )
    )
    print(
        "complement: "
        + ", ".join(
            f"r={i+1}:{100.0 * complement_cumulative[i]:.4f}%"
            for i in range(min(len(complement_cumulative), len(empirical_residual)))
        )
    )

    print("\n== Shadow Operator Audit ==")
    for audit in (empirical_audit, geometric_audit, complement_audit):
        print(f"-- {audit.label} --")
        print(f"dimension={audit.dimension}")
        print("basis sums =", [f"{x:.12e}" for x in audit.basis_sums])
        print(f"operator norm = {audit.operator_norm:.12e}")
        if audit.decimal_basis_sums is not None and audit.decimal_operator_norm is not None:
            print("basis sums (decimal) =", [format(x, "e") for x in audit.decimal_basis_sums])
            print(f"operator norm (decimal) = {format(audit.decimal_operator_norm, 'e')}")

    print("\n== Space Overlaps ==")
    for j, vec in enumerate(empirical_basis.basis):
        best = max(abs(corr(vec, g)) for g in geometric_basis.basis) if geometric_basis.basis else 0.0
        print(f"empirical basis {j} best overlap with geometric = {best:.6f}")


if __name__ == "__main__":
    main()
