#!/usr/bin/env python3
"""
Dictionary experiments for the exact minor singularity family.

This script answers two questions on the exact repo object:

1. How well do simple explicit atoms correlate with the exact rank-r SVD basis?
2. Among a modest explicit dictionary, which small subspaces best capture the
   exact `coeffArith` family energy and preserve the downstream shadow collapse?

It reuses the exact object construction from:
  scripts/experiments/exp_q0_minor_singularity_exact_harness.py
"""

from __future__ import annotations

import argparse
import itertools
import math
from dataclasses import dataclass

from exp_q0_minor_singularity_exact_harness import (
    H,
    Q0,
    WeightBackend,
    build_family_vectors,
    build_weighted_slices,
    cache_path,
    canonical_window_points,
    coeffarith_alpha,
    compute_S_all,
    dot,
    ensure_weights,
    gram_schmidt_orthonormalize,
    mertens_weighted,
    mobius_phi_sieve,
    mobius_sieve,
    save_basis_file,
    sum_by_s,
    svd_basis_from_family_vectors,
    weight_stats,
)


@dataclass
class Atom:
    label: str
    values: list[float]


def alternating_dictionary(
    *,
    support: list[int],
    max_freq: int,
    max_degree: int = 0,
) -> list[Atom]:
    atoms: list[Atom] = []
    denom = 4.0 * H
    ambient = max(abs(t) for t in support) if support else 1

    def carrier(t: int) -> float:
        return 1.0 if (t % 2 == 0) else -1.0

    for d in range(max_degree + 1):
        vec = []
        for t in support:
            z = t / float(ambient)
            vec.append(carrier(t) * (z**d))
        atoms.append(Atom(f"alt_poly_{d}", vec))
    for k in range(1, max_freq + 1):
        for d in range(max_degree + 1):
            cos_vec = []
            sin_vec = []
            for t in support:
                base = carrier(t)
                z = t / float(ambient)
                phase = math.pi * k * ((t + 3.0 * H) / denom)
                amp = z**d
                cos_vec.append(base * amp * math.cos(phase))
                sin_vec.append(base * amp * math.sin(phase))
            atoms.append(Atom(f"alt_poly_{d}_cos_{k}", cos_vec))
            atoms.append(Atom(f"alt_poly_{d}_sin_{k}", sin_vec))
    return atoms


def alternating_window_dictionary(
    *,
    support: list[int],
    centers: list[float],
    halfwidth: float,
    max_freq: int,
) -> list[Atom]:
    atoms: list[Atom] = []
    denom = 4.0 * H

    def carrier(t: int) -> float:
        return 1.0 if (t % 2 == 0) else -1.0

    def hat(t: int, c: float) -> float:
        u = abs(t - c) / halfwidth
        return 0.0 if u >= 1.0 else 1.0 - u

    for c in centers:
        env = [hat(t, c) for t in support]
        atoms.append(Atom(f"alt_win_const_{c/H:.2f}H", [carrier(t) * e for t, e in zip(support, env)]))
        for k in range(1, max_freq + 1):
            cos_vec = []
            sin_vec = []
            for t, e in zip(support, env):
                base = carrier(t) * e
                phase = math.pi * k * ((t + 3.0 * H) / denom)
                cos_vec.append(base * math.cos(phase))
                sin_vec.append(base * math.sin(phase))
            atoms.append(Atom(f"alt_win_cos_{k}_{c/H:.2f}H", cos_vec))
            atoms.append(Atom(f"alt_win_sin_{k}_{c/H:.2f}H", sin_vec))
    return atoms


def alternating_window_poly_dictionary(
    *,
    support: list[int],
    centers: list[float],
    halfwidth: float,
    max_freq: int,
    max_degree: int,
) -> list[Atom]:
    atoms: list[Atom] = []

    def carrier(t: int) -> float:
        return 1.0 if (t % 2 == 0) else -1.0

    def hat_and_local(t: int, c: float) -> tuple[float, float]:
        z = (t - c) / halfwidth
        u = abs(z)
        w = 0.0 if u >= 1.0 else 1.0 - u
        return w, z

    for c in centers:
        for d in range(max_degree + 1):
            vec = []
            for t in support:
                w, z = hat_and_local(t, c)
                vec.append(carrier(t) * w * (z ** d))
            atoms.append(Atom(f"alt_wpoly_{d}_{c/H:.2f}H", vec))
        for k in range(1, max_freq + 1):
            for d in range(max_degree + 1):
                cos_vec = []
                sin_vec = []
                for t in support:
                    w, z = hat_and_local(t, c)
                    base = carrier(t) * w * (z ** d)
                    phase = math.pi * k * z
                    cos_vec.append(base * math.cos(phase))
                    sin_vec.append(base * math.sin(phase))
                atoms.append(Atom(f"alt_wpoly_{d}_cos_{k}_{c/H:.2f}H", cos_vec))
                atoms.append(Atom(f"alt_wpoly_{d}_sin_{k}_{c/H:.2f}H", sin_vec))
    return atoms


def normalize(vec: list[float]) -> list[float]:
    nrm = math.sqrt(max(dot(vec, vec), 0.0))
    if nrm <= 1e-18:
        return [0.0 for _ in vec]
    return [x / nrm for x in vec]


def top_correlations(
    *,
    svd_basis: list[list[float]],
    atoms: list[Atom],
    top_m: int,
) -> list[list[tuple[str, float]]]:
    atom_normed = [(atom.label, normalize(atom.values)) for atom in atoms]
    out: list[list[tuple[str, float]]] = []
    for b in svd_basis:
        cur = sorted(
            ((label, abs(dot(b, avec))) for label, avec in atom_normed),
            key=lambda x: x[1],
            reverse=True,
        )[:top_m]
        out.append(cur)
    return out


def solve_small_system(a: list[list[float]], b: list[float]) -> list[float]:
    n = len(a)
    aug = [row[:] + [rhs] for row, rhs in zip(a, b)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-18:
            return [0.0] * n
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        piv = aug[col][col]
        for j in range(col, n + 1):
            aug[col][j] /= piv
        for r in range(n):
            if r == col:
                continue
            fac = aug[r][col]
            if fac == 0.0:
                continue
            for j in range(col, n + 1):
                aug[r][j] -= fac * aug[col][j]
    return [aug[i][n] for i in range(n)]


@dataclass
class ComboResult:
    labels: tuple[str, ...]
    capture_ratio: float
    residual_ratio: float
    shadow_ratio: float


def best_dictionary_combos(
    *,
    atoms: list[Atom],
    family_vectors: list[list[float]],
    combo_size: int,
    top_k: int,
) -> list[ComboResult]:
    full_energy = sum(dot(v, v) for v in family_vectors)
    full_sums = [sum(v) for v in family_vectors]
    atom_grams = [[dot(a.values, b.values) for b in atoms] for a in atoms]
    atom_sums = [sum(a.values) for a in atoms]
    cross = [[dot(a.values, v) for v in family_vectors] for a in atoms]

    results: list[ComboResult] = []
    for combo in itertools.combinations(range(len(atoms)), combo_size):
        gram = [[atom_grams[i][j] for j in combo] for i in combo]
        captured = 0.0
        shadow = 0.0
        sum_coeffs = [atom_sums[i] for i in combo]
        for slice_idx, full_sum in enumerate(full_sums):
            rhs = [cross[i][slice_idx] for i in combo]
            coeffs = solve_small_system(gram, rhs)
            cap_slice = sum(c * r for c, r in zip(coeffs, rhs))
            captured += cap_slice
            approx_sum = sum(c * s for c, s in zip(coeffs, sum_coeffs))
            resid_sum = full_sum - approx_sum
            shadow += resid_sum * resid_sum
        residual = max(full_energy - captured, 0.0)
        capture_ratio = 0.0 if full_energy == 0.0 else captured / full_energy
        residual_ratio = 0.0 if full_energy == 0.0 else residual / full_energy
        shadow_ratio = 0.0 if full_energy == 0.0 else shadow / full_energy
        results.append(
            ComboResult(
                labels=tuple(atoms[i].label for i in combo),
                capture_ratio=capture_ratio,
                residual_ratio=residual_ratio,
                shadow_ratio=shadow_ratio,
            )
        )
    results.sort(key=lambda r: (r.capture_ratio, -r.shadow_ratio), reverse=True)
    return results[:top_k]


def main() -> None:
    parser = argparse.ArgumentParser(description="Dictionary experiments on exact coeffArith family.")
    parser.add_argument("--X", type=int, required=True)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--backend", choices=["exact", "hybrid"], default="exact")
    parser.add_argument("--qsplit", type=int, default=2000)
    parser.add_argument("--svd-rank", type=int, default=3)
    parser.add_argument(
        "--dictionary",
        choices=["alt-harmonic", "alt-polyharmonic", "alt-windowed", "alt-windowed-poly"],
        default="alt-harmonic",
    )
    parser.add_argument("--max-freq", type=int, default=8)
    parser.add_argument("--max-degree", type=int, default=0)
    parser.add_argument("--window-centers", type=str, default="-2.5,-2.0,-1.5,-1.0,-0.5,0.0")
    parser.add_argument("--window-halfwidth", type=float, default=0.75)
    parser.add_argument("--combo-sizes", type=str, default="3,4")
    parser.add_argument("--top-combos", type=int, default=5)
    parser.add_argument("--top-correlations", type=int, default=6)
    parser.add_argument("--export-basis", type=str, default=None)
    args = parser.parse_args()

    X = args.X
    window = canonical_window_points(X)
    combo_sizes = [int(x.strip()) for x in args.combo_sizes.split(",") if x.strip()]

    print("== Parameters ==")
    print(
        f"X={X:,} backend={args.backend} jobs={args.jobs} svd_rank={args.svd_rank} "
        f"dictionary={args.dictionary} max_freq={args.max_freq} max_degree={args.max_degree} "
        f"combo_sizes={combo_sizes}"
    )
    print(f"window={window}")

    print("[build] precomputing exact arithmetic core by sum-level regrouping")
    by_s = sum_by_s(X)
    print(f"[build] distinct sum levels: {len(by_s):,}")

    required_abs_t = set(range(0, X + H + 1))
    print(f"[build] distinct |t| values needed for coeffArith: {len(required_abs_t):,}")

    mu_q0, phi_q0 = mobius_phi_sieve(Q0)
    if args.backend == "exact":
        backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
    else:
        if not (1 <= args.qsplit <= Q0):
            raise SystemExit("Require 1 <= qsplit <= Q0.")
        mu_small, phi_small = mobius_phi_sieve(args.qsplit)
        mu0 = mobius_sieve(Q0)
        mus = mobius_sieve(args.qsplit)
        s_q0 = compute_S_all(Q=Q0, Tmax=X + H, mu=mu0)
        s_qs = compute_S_all(Q=args.qsplit, Tmax=X + H, mu=mus)
        backend = WeightBackend(
            kind="hybrid",
            X=X,
            mu_q0=mu_q0,
            phi_q0=phi_q0,
            qsplit=args.qsplit,
            mu_small=mu_small,
            phi_small=phi_small,
            s_q0=s_q0,
            s_qs=s_qs,
        )

    cpath = cache_path(X, args.backend, args.qsplit if args.backend == "hybrid" else None)
    weights = ensure_weights(
        required_abs_t=required_abs_t,
        backend=backend,
        jobs=max(1, args.jobs),
        cache_file=cpath,
    )
    slices = build_weighted_slices(X, window, weights, by_s)
    wstats = weight_stats(X, weights)
    support, vectors = build_family_vectors(
        X=X,
        obj="coeffarith",
        slices=slices,
        weights=weights,
        wstats=wstats,
    )

    basis, cumulative = svd_basis_from_family_vectors(
        support=support,
        vectors=vectors,
        rank=args.svd_rank,
        label=f"coeffarith-family-svd-X{X}-rank{args.svd_rank}",
    )
    print(
        "[svd] cumulative captures by rank: "
        + ", ".join(
            f"r={i+1}:{100.0*cumulative[i]:.4f}%"
            for i in range(min(len(cumulative), len(vectors)))
        )
    )
    if args.export_basis is not None:
        save_basis_file(args.export_basis, basis)
        print(f"[svd] wrote orthonormal basis to {args.export_basis}")

    if args.dictionary == "alt-windowed":
        centers = [float(x.strip()) * H for x in args.window_centers.split(",") if x.strip()]
        atoms = alternating_window_dictionary(
            support=support,
            centers=centers,
            halfwidth=args.window_halfwidth * H,
            max_freq=args.max_freq,
        )
    elif args.dictionary == "alt-windowed-poly":
        centers = [float(x.strip()) * H for x in args.window_centers.split(",") if x.strip()]
        atoms = alternating_window_poly_dictionary(
            support=support,
            centers=centers,
            halfwidth=args.window_halfwidth * H,
            max_freq=args.max_freq,
            max_degree=args.max_degree,
        )
    else:
        atoms = alternating_dictionary(
            support=support,
            max_freq=args.max_freq,
            max_degree=(args.max_degree if args.dictionary == "alt-polyharmonic" else 0),
        )
    print(f"[dict] built {len(atoms)} {args.dictionary} atoms")

    print("\n== Basis/SVD Correlations ==")
    corr = top_correlations(
        svd_basis=basis.basis,
        atoms=atoms,
        top_m=args.top_correlations,
    )
    for i, row in enumerate(corr):
        formatted = ", ".join(f"{label}:{score:.6f}" for label, score in row)
        print(f"svd[{i}] -> {formatted}")

    print("\n== Best Dictionary Combos ==")
    for combo_size in combo_sizes:
        print(f"-- combo size {combo_size} --")
        best = best_dictionary_combos(
            atoms=atoms,
            family_vectors=vectors,
            combo_size=combo_size,
            top_k=args.top_combos,
        )
        for j, res in enumerate(best, start=1):
            print(
                f"#{j} labels={res.labels} "
                f"capture={100.0 * res.capture_ratio:.6f}% "
                f"residual={100.0 * res.residual_ratio:.6f}% "
                f"shadow={100.0 * res.shadow_ratio:.6e}%"
            )


if __name__ == "__main__":
    main()
