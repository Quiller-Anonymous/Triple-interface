#!/usr/bin/env python3
"""
Exact-weight minor singularity harness on the repo object.

Purpose
-------
This script evaluates the exact raw weighted minor family, the exact centered family,
and the exact weight-regressed arithmetic family
corresponding to the Lean objects:

  weightedMinorCoeff
  coeffCentered
  coeffArith

from:
  Goldbach/Cert/MajorArcModules/Q0MinorSingularityBridge.lean
  Goldbach/Cert/MajorArcModules/Q0MinorSingularityHarness.lean

It is intended to make in-repo Stage I feasibility checks easier by reproducing the same
bookkeeping on the actual hard minor weight, rather than on an old truncated-q toy model.

Scope
-----
This script currently supports:
  - the exact raw weighted family (`weighted`)
  - the exact centered family (`centered`)
  - the exact weight-regressed arithmetic family (`coeffarith`)

For `coeffarith`, the exact regression layer is evaluated on the true ambient support
`tSupport(X+H) \\ {0}`. This is heavier than the raw/centered passes because it needs the full
ambient weight-only statistics, not just the sparse support touched by the exact weighted family.

Important
---------
The exact hard minor weight

  minorArcWeightFourier X Δ_canon t

is expensive to evaluate. This script therefore supports:
  - persistent on-disk caching, and
  - an optional hybrid backend

The default backend is `exact`.

This is still an experiment harness. It does not generate a Lean certificate.
It can, however:
  - export the exact windowed family matrix for a chosen object, and
  - evaluate a supplied low-rank basis on that exact family.
"""

from __future__ import annotations

import argparse
import math
import multiprocessing as mp
import pickle
from array import array
from bisect import bisect_left, bisect_right
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


H = 10_000
Q0 = 30_000
DELTA_CANON = 1.0
Ucut = H + (H + 99) // 100
CACHE_DIR = Path("scripts/experiments/cache")


def sieve_primes_mask(n: int) -> bytearray:
    is_prime = bytearray(b"\x01") * (n + 1)
    is_prime[0:2] = b"\x00\x00"
    limit = int(math.isqrt(n))
    for p in range(2, limit + 1):
        if is_prime[p]:
            start = p * p
            is_prime[start : n + 1 : p] = b"\x00" * (((n - start) // p) + 1)
    return is_prime


def prime_window_payload(X: int) -> list[tuple[int, float]]:
    lo = X // 2 - H
    hi = X // 2 + H
    if lo < 2:
        lo = 2
    is_prime = sieve_primes_mask(hi)
    w_scale = 1.0 / (math.log(X) * (2 * H + 1))
    return [(n, w_scale * math.log(n)) for n in range(lo, hi + 1) if is_prime[n]]


def q0_norm_factor(N: int) -> float:
    return (1.0 / 800.0) * (1.0 / (math.log(N) ** 2))


def k_full_on_sbg(k: int) -> float:
    if abs(k) > H:
        return 0.0
    return max(1.0 - (abs(k) / float(Ucut)), 0.0) / float(Ucut)


def mobius_sieve(n: int) -> list[int]:
    mu = [0] * (n + 1)
    is_comp = [False] * (n + 1)
    primes: list[int] = []
    mu[1] = 1
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            ip = i * p
            if ip > n:
                break
            is_comp[ip] = True
            if i % p == 0:
                mu[ip] = 0
                break
            mu[ip] = -mu[i]
    return mu


def mobius_phi_sieve(n: int) -> tuple[list[int], list[int]]:
    mu = [0] * (n + 1)
    phi = [0] * (n + 1)
    is_comp = [False] * (n + 1)
    primes: list[int] = []
    mu[1] = 1
    phi[1] = 1
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
            phi[i] = i - 1
        for p in primes:
            ip = i * p
            if ip > n:
                break
            is_comp[ip] = True
            if i % p == 0:
                mu[ip] = 0
                phi[ip] = phi[i] * p
                break
            mu[ip] = -mu[i]
            phi[ip] = phi[i] * (p - 1)
    return mu, phi


def mertens_weighted(mu: list[int]) -> list[float]:
    out = [0.0] * len(mu)
    acc = 0.0
    for n in range(1, len(mu)):
        acc += mu[n] / n
        out[n] = acc
    return out


def compute_S_all(*, Q: int, Tmax: int, mu: list[int]) -> array:
    m = mertens_weighted(mu)
    s_arr = array("d", [0.0]) * (Tmax + 1)
    max_d = min(Q, Tmax)
    for d in range(1, max_d + 1):
        coef = m[Q // d]
        for t in range(d, Tmax + 1, d):
            s_arr[t] += coef
    return s_arr


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def major_zero_mode(X: int, phi: list[int]) -> float:
    return (1.0 / X) + (2.0 / X) * sum(phi[q] / q for q in range(2, Q0 + 1))


def major_w_hat_exact(*, X: int, t: int, mu: list[int], phi: list[int]) -> float:
    s = 0.0
    two_pi_t_over_x = 2.0 * math.pi * t / X
    for q in range(1, Q0 + 1):
        cq = ramanujan_sum(q, t, mu, phi)
        if cq:
            s += cq * math.sin(two_pi_t_over_x / q)
    return s / (math.pi * t)


def major_w_hat_hybrid(
    *,
    X: int,
    t: int,
    qsplit: int,
    mu_small: list[int],
    phi_small: list[int],
    s_q0: array,
    s_qs: array,
) -> float:
    sum_small = 0.0
    two_pi_t_over_x = 2.0 * math.pi * t / X
    for q in range(1, qsplit + 1):
        cq = ramanujan_sum(q, t, mu_small, phi_small)
        if cq:
            sum_small += cq * math.sin(two_pi_t_over_x / q)
    exact_small = sum_small / (math.pi * t)
    tail_lin = (2.0 / X) * (s_q0[t] - s_qs[t])
    return exact_small + tail_lin


@dataclass
class WeightBackend:
    kind: str
    X: int
    mu_q0: list[int]
    phi_q0: list[int]
    qsplit: int | None = None
    mu_small: list[int] | None = None
    phi_small: list[int] | None = None
    s_q0: array | None = None
    s_qs: array | None = None

    def major_weight(self, t: int) -> float:
        if t == 0:
            return major_zero_mode(self.X, self.phi_q0)
        if self.kind == "exact":
            return major_w_hat_exact(X=self.X, t=t, mu=self.mu_q0, phi=self.phi_q0)
        if self.kind == "hybrid":
            assert self.qsplit is not None
            assert self.mu_small is not None and self.phi_small is not None
            assert self.s_q0 is not None and self.s_qs is not None
            return major_w_hat_hybrid(
                X=self.X,
                t=t,
                qsplit=self.qsplit,
                mu_small=self.mu_small,
                phi_small=self.phi_small,
                s_q0=self.s_q0,
                s_qs=self.s_qs,
            )
        raise ValueError(f"unknown backend kind: {self.kind}")

    def minor_weight(self, t: int) -> float:
        if t == 0:
            return 1.0 - self.major_weight(0)
        return -self.major_weight(abs(t))


_WORKER_BACKEND: WeightBackend | None = None


def _init_worker(backend: WeightBackend) -> None:
    global _WORKER_BACKEND
    _WORKER_BACKEND = backend


def _compute_minor_weight_worker(t: int) -> tuple[int, float]:
    assert _WORKER_BACKEND is not None
    return t, _WORKER_BACKEND.minor_weight(t)


def cache_path(X: int, backend: str, qsplit: int | None) -> Path:
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    suffix = f"_qsplit{qsplit}" if backend == "hybrid" and qsplit is not None else ""
    return CACHE_DIR / f"minor_weight_X{X}_Q0{Q0}_{backend}{suffix}.pkl"


def load_weight_cache(path: Path) -> dict[int, float]:
    if not path.exists():
        return {}
    with path.open("rb") as fh:
        return pickle.load(fh)


def save_weight_cache(path: Path, cache: dict[int, float]) -> None:
    with path.open("wb") as fh:
        pickle.dump(cache, fh, protocol=pickle.HIGHEST_PROTOCOL)


def ensure_weights(
    *,
    required_abs_t: Iterable[int],
    backend: WeightBackend,
    jobs: int,
    cache_file: Path,
) -> dict[int, float]:
    cache = load_weight_cache(cache_file)
    needed = sorted({int(t) for t in required_abs_t if int(t) >= 0})
    missing = [t for t in needed if t not in cache]
    if not missing:
        return cache
    print(f"[weights] cache miss count: {len(missing)}")
    if jobs <= 1 or len(missing) <= 1:
        for idx, t in enumerate(missing, start=1):
            cache[t] = backend.minor_weight(t)
            if idx % 500 == 0 or idx == len(missing):
                print(f"[weights] computed {idx}/{len(missing)}")
                save_weight_cache(cache_file, cache)
        return cache
    with mp.Pool(processes=jobs, initializer=_init_worker, initargs=(backend,)) as pool:
        for idx, (t, wt) in enumerate(pool.imap_unordered(_compute_minor_weight_worker, missing), start=1):
            cache[t] = wt
            if idx % 500 == 0 or idx == len(missing):
                print(f"[weights] computed {idx}/{len(missing)}")
                save_weight_cache(cache_file, cache)
    return cache


def canonical_window_points(X: int) -> list[int]:
    return [X, X + H // 4, X + H // 2, X + 3 * H // 4, X + H]


def sum_by_s(X: int) -> dict[int, float]:
    payload = prime_window_payload(X)
    primes = [n for n, _ in payload]
    vals = [a for _, a in payload]
    out: dict[int, float] = {}
    for i, n in enumerate(primes):
        lo = bisect_left(primes, n - H)
        hi = bisect_right(primes, n + H)
        ai = vals[i]
        for j in range(lo, hi):
            m = primes[j]
            contrib = ai * vals[j] * k_full_on_sbg(m - n)
            if contrib == 0.0:
                continue
            s = n + m
            out[s] = out.get(s, 0.0) + contrib
    return out


@dataclass
class SliceData:
    N: int
    raw0: float
    raw_nonzero: dict[int, float]
    nonzero_sum: float
    mean_nonzero: float


@dataclass
class WeightStats:
    ambient_max: int
    m_nonzero: int
    mean_nonzero: float
    sum_nonzero: float
    norm_sq_centered: float


def build_weighted_slices(X: int, window: list[int], weights: dict[int, float], by_s: dict[int, float]) -> list[SliceData]:
    m_nonzero = 2 * (X + H)
    out: list[SliceData] = []
    s_items = list(by_s.items())
    for N in window:
        q0 = q0_norm_factor(N)
        raw0 = q0 * by_s.get(N, 0.0) * weights[0]
        raw_nonzero: dict[int, float] = {}
        nonzero_sum = 0.0
        for s, core in s_items:
            t = s - N
            if t == 0:
                continue
            wt = weights[abs(t)]
            val = q0 * core * wt
            if val != 0.0:
                raw_nonzero[t] = val
                nonzero_sum += val
        mean_nonzero = nonzero_sum / m_nonzero
        out.append(SliceData(N=N, raw0=raw0, raw_nonzero=raw_nonzero, nonzero_sum=nonzero_sum, mean_nonzero=mean_nonzero))
    return out


def weight_stats(X: int, weights: dict[int, float]) -> WeightStats:
    ambient_max = X + H
    m_nonzero = 2 * ambient_max
    sum_pos = sum(weights[k] for k in range(1, ambient_max + 1))
    sum_nonzero = 2.0 * sum_pos
    mean_nonzero = sum_nonzero / m_nonzero
    sum_sq_pos = sum(weights[k] * weights[k] for k in range(1, ambient_max + 1))
    sum_sq_nonzero = 2.0 * sum_sq_pos
    norm_sq_centered = sum_sq_nonzero - m_nonzero * (mean_nonzero ** 2)
    return WeightStats(
        ambient_max=ambient_max,
        m_nonzero=m_nonzero,
        mean_nonzero=mean_nonzero,
        sum_nonzero=sum_nonzero,
        norm_sq_centered=norm_sq_centered,
    )


def coeffarith_alpha(sl: SliceData, wstats: WeightStats, weights: dict[int, float]) -> float:
    numer = 0.0
    for t, raw in sl.raw_nonzero.items():
        numer += raw * weights[abs(t)]
    numer -= sl.nonzero_sum * wstats.mean_nonzero
    if wstats.norm_sq_centered == 0.0:
        return 0.0
    return numer / wstats.norm_sq_centered


def coeffarith_mode_energy_info(
    X: int,
    slices: list[SliceData],
    weights: dict[int, float],
    wstats: WeightStats,
) -> dict[int, float]:
    energy: dict[int, float] = {0: 0.0}
    alphas = [coeffarith_alpha(sl, wstats, weights) for sl in slices]
    for t in range(1, wstats.ambient_max + 1):
        wt_centered = weights[t] - wstats.mean_nonzero
        e_pos = 0.0
        e_neg = 0.0
        for sl, alpha in zip(slices, alphas):
            pos_raw = sl.raw_nonzero.get(t, 0.0)
            neg_raw = sl.raw_nonzero.get(-t, 0.0)
            pos_val = (pos_raw - sl.mean_nonzero) - alpha * wt_centered
            neg_val = (neg_raw - sl.mean_nonzero) - alpha * wt_centered
            e_pos += pos_val * pos_val
            e_neg += neg_val * neg_val
        energy[t] = e_pos
        energy[-t] = e_neg
    return energy


def weighted_mode_energies(slices: list[SliceData]) -> dict[int, float]:
    energy: dict[int, float] = {}
    for sl in slices:
        if sl.raw0 != 0.0:
            energy[0] = energy.get(0, 0.0) + sl.raw0 * sl.raw0
        for t, val in sl.raw_nonzero.items():
            energy[t] = energy.get(t, 0.0) + val * val
    return energy


def centered_mode_energy_info(X: int, slices: list[SliceData]) -> tuple[dict[int, float], float]:
    base = sum(sl.mean_nonzero * sl.mean_nonzero for sl in slices)
    energy: dict[int, float] = {0: 0.0}
    union_nonzero = set()
    for sl in slices:
        union_nonzero.update(sl.raw_nonzero)
    for t in union_nonzero:
        e = base
        for sl in slices:
            if t in sl.raw_nonzero:
                raw = sl.raw_nonzero[t]
                e += (raw - sl.mean_nonzero) ** 2 - (sl.mean_nonzero ** 2)
        energy[t] = e
    return energy, base


def ordered_modes_from_energy(
    *,
    X: int,
    energy: dict[int, float],
    fill_base_modes: bool,
) -> list[int]:
    distinguished = sorted(energy.items(), key=lambda kv: (-kv[1], abs(kv[0]), kv[0]))
    out = [t for t, _ in distinguished]
    if not fill_base_modes:
        return out
    ambient_max = X + H
    used = set(out)
    for t in range(1, ambient_max + 1):
        for cand in (t, -t):
            if cand not in used:
                out.append(cand)
                used.add(cand)
    return out


@dataclass
class Report:
    full_family_energy: float
    captured_family_energy: float
    residual_family_energy: float
    shadow_residual_energy: float

    @property
    def capture_ratio(self) -> float:
        return 0.0 if self.full_family_energy == 0.0 else self.captured_family_energy / self.full_family_energy

    @property
    def residual_ratio(self) -> float:
        return 0.0 if self.full_family_energy == 0.0 else self.residual_family_energy / self.full_family_energy

    @property
    def shadow_residual_ratio(self) -> float:
        return 0.0 if self.full_family_energy == 0.0 else self.shadow_residual_energy / self.full_family_energy


@dataclass
class BasisData:
    support: list[int]
    basis: list[list[float]]
    orthonormal: bool
    label: str | None = None


@dataclass
class LeaveOneOutEntry:
    held_out_index: int
    held_out_N: int
    training_rank: int
    captured_energy: float
    residual_energy: float
    shadow_residual_energy: float

    @property
    def capture_ratio(self) -> float:
        total = self.captured_energy + self.residual_energy
        return 0.0 if total == 0.0 else self.captured_energy / total

    @property
    def residual_ratio(self) -> float:
        total = self.captured_energy + self.residual_energy
        return 0.0 if total == 0.0 else self.residual_energy / total

    @property
    def shadow_residual_ratio(self) -> float:
        total = self.captured_energy + self.residual_energy
        return 0.0 if total == 0.0 else self.shadow_residual_energy / total


def alternating_dct_basis(
    *,
    support: list[int],
    rank: int,
    orthonormalize: bool = True,
) -> BasisData:
    basis_vectors: list[list[float]] = []
    denom = 4.0 * H
    for j in range(rank):
        vec = []
        for t in support:
            carrier = 1.0 if (t % 2 == 0) else -1.0
            phase = math.pi * j * ((t + 3.0 * H) / denom)
            vec.append(carrier * math.cos(phase))
        basis_vectors.append(vec)
    if orthonormalize:
        basis_vectors = gram_schmidt_orthonormalize(basis_vectors)
    return BasisData(
        support=support,
        basis=basis_vectors,
        orthonormal=orthonormalize,
        label=f"alt-dct-rank{rank}" + ("-orthonormalized" if orthonormalize else ""),
    )


def alternating_harmonic_basis(
    *,
    support: list[int],
    rank: int,
    orthonormalize: bool = True,
) -> BasisData:
    basis_vectors: list[list[float]] = []
    denom = 4.0 * H
    slots: list[tuple[str, int]] = [("const", 0)]
    k = 1
    while len(slots) < rank:
        slots.append(("cos", k))
        if len(slots) < rank:
            slots.append(("sin", k))
        k += 1
    for kind, j in slots[:rank]:
        vec = []
        for t in support:
            carrier = 1.0 if (t % 2 == 0) else -1.0
            phase = math.pi * j * ((t + 3.0 * H) / denom)
            if kind == "const":
                val = carrier
            elif kind == "cos":
                val = carrier * math.cos(phase)
            elif kind == "sin":
                val = carrier * math.sin(phase)
            else:
                raise ValueError(f"unknown harmonic slot kind: {kind}")
            vec.append(val)
        basis_vectors.append(vec)
    if orthonormalize:
        basis_vectors = gram_schmidt_orthonormalize(basis_vectors)
    return BasisData(
        support=support,
        basis=basis_vectors,
        orthonormal=orthonormalize,
        label=f"alt-harmonic-rank{rank}" + ("-orthonormalized" if orthonormalize else ""),
    )


def weighted_report(X: int, slices: list[SliceData], selected: set[int]) -> Report:
    full = 0.0
    captured = 0.0
    shadow = 0.0
    for sl in slices:
        full_slice = sl.raw0 + sl.nonzero_sum
        full += sl.raw0 * sl.raw0
        if 0 in selected:
            captured += sl.raw0 * sl.raw0
            selected_sum = sl.raw0
        else:
            selected_sum = 0.0
        for t, val in sl.raw_nonzero.items():
            sq = val * val
            full += sq
            if t in selected:
                captured += sq
                selected_sum += val
        residual_slice = full_slice - selected_sum
        shadow += residual_slice * residual_slice
    return Report(
        full_family_energy=full,
        captured_family_energy=captured,
        residual_family_energy=full - captured,
        shadow_residual_energy=shadow,
    )


def centered_report(X: int, slices: list[SliceData], selected: set[int]) -> Report:
    m_nonzero = 2 * (X + H)
    full = 0.0
    captured = 0.0
    shadow = 0.0
    for sl in slices:
        actual = sl.raw_nonzero
        actual_count = len(actual)
        full_slice_energy = 0.0
        selected_sum = 0.0
        selected_energy = 0.0
        if 0 in selected:
            pass
        for t, raw in actual.items():
            centered_val = raw - sl.mean_nonzero
            sq = centered_val * centered_val
            full_slice_energy += sq
            if t in selected:
                selected_energy += sq
                selected_sum += centered_val
        absent_count = m_nonzero - actual_count
        full_slice_energy += absent_count * (sl.mean_nonzero ** 2)
        selected_absent_nonzero = len([t for t in selected if t != 0 and t not in actual])
        if selected_absent_nonzero:
            selected_energy += selected_absent_nonzero * (sl.mean_nonzero ** 2)
            selected_sum += selected_absent_nonzero * (-sl.mean_nonzero)
        full += full_slice_energy
        captured += selected_energy
        # The full centered slice sum over the ambient support is exactly 0.
        residual_slice = -selected_sum
        shadow += residual_slice * residual_slice
    return Report(
        full_family_energy=full,
        captured_family_energy=captured,
        residual_family_energy=full - captured,
        shadow_residual_energy=shadow,
    )


def coeffarith_report(
    X: int,
    slices: list[SliceData],
    weights: dict[int, float],
    wstats: WeightStats,
    selected: set[int],
) -> Report:
    full = 0.0
    captured = 0.0
    shadow = 0.0
    for sl in slices:
        alpha = coeffarith_alpha(sl, wstats, weights)
        numer = alpha * wstats.norm_sq_centered
        centered_full = 0.0
        actual = sl.raw_nonzero
        actual_count = len(actual)
        for raw in actual.values():
            centered_val = raw - sl.mean_nonzero
            centered_full += centered_val * centered_val
        centered_full += (wstats.m_nonzero - actual_count) * (sl.mean_nonzero ** 2)
        full_slice_energy = centered_full - alpha * numer
        full += full_slice_energy

        selected_sum = 0.0
        selected_energy = 0.0
        for t in selected:
            if t == 0:
                continue
            raw = actual.get(t, 0.0)
            wt_centered = weights[abs(t)] - wstats.mean_nonzero
            arith_val = (raw - sl.mean_nonzero) - alpha * wt_centered
            selected_sum += arith_val
            selected_energy += arith_val * arith_val
        captured += selected_energy
        residual_slice = -selected_sum
        shadow += residual_slice * residual_slice
    return Report(
        full_family_energy=full,
        captured_family_energy=captured,
        residual_family_energy=full - captured,
        shadow_residual_energy=shadow,
    )


def object_support(X: int, slices: list[SliceData], obj: str) -> list[int]:
    if obj == "zeromode":
        return [0]
    if obj == "meanchannel":
        ambient_max = X + H
        return [t for t in range(-ambient_max, ambient_max + 1) if t != 0]
    if obj == "routevisible":
        ambient_max = X + H
        return [t for t in range(-ambient_max, ambient_max + 1)]
    if obj == "weighted":
        supp = {0}
        for sl in slices:
            supp.update(sl.raw_nonzero)
        return sorted(supp)
    ambient_max = X + H
    return [t for t in range(-ambient_max, ambient_max + 1) if t != 0]


def object_value(
    *,
    obj: str,
    t: int,
    sl: SliceData,
    weights: dict[int, float],
    wstats: WeightStats | None,
    alpha: float | None,
) -> float:
    if obj == "zeromode":
        return sl.raw0 if t == 0 else 0.0
    if obj == "meanchannel":
        if t == 0:
            return 0.0
        return sl.mean_nonzero
    if obj == "routevisible":
        if t == 0:
            return sl.raw0
        return sl.mean_nonzero
    if obj == "weighted":
        if t == 0:
            return sl.raw0
        return sl.raw_nonzero.get(t, 0.0)
    if obj == "centered":
        if t == 0:
            return 0.0
        return sl.raw_nonzero.get(t, 0.0) - sl.mean_nonzero
    if obj == "coeffarith":
        assert wstats is not None
        assert alpha is not None
        if t == 0:
            return 0.0
        wt_centered = weights[abs(t)] - wstats.mean_nonzero
        return (sl.raw_nonzero.get(t, 0.0) - sl.mean_nonzero) - alpha * wt_centered
    raise ValueError(f"unknown object: {obj}")


def object_slice_vector(
    *,
    obj: str,
    support: list[int],
    sl: SliceData,
    weights: dict[int, float],
    wstats: WeightStats | None,
    alpha: float | None,
) -> list[float]:
    return [
        object_value(obj=obj, t=t, sl=sl, weights=weights, wstats=wstats, alpha=alpha)
        for t in support
    ]


def build_family_vectors(
    *,
    X: int,
    obj: str,
    slices: list[SliceData],
    weights: dict[int, float],
    wstats: WeightStats | None,
) -> tuple[list[int], list[list[float]]]:
    support = object_support(X, slices, obj)
    if obj == "coeffarith":
        assert wstats is not None
        alphas: list[float | None] = [coeffarith_alpha(sl, wstats, weights) for sl in slices]
    else:
        alphas = [None for _ in slices]
    vectors = [
        object_slice_vector(
            obj=obj,
            support=support,
            sl=sl,
            weights=weights,
            wstats=wstats,
            alpha=alpha,
        )
        for sl, alpha in zip(slices, alphas)
    ]
    return support, vectors


def export_family_payload(
    *,
    X: int,
    obj: str,
    window: list[int],
    support: list[int],
    vectors: list[list[float]],
) -> dict[str, object]:
    return {
        "X": X,
        "object": obj,
        "window": window,
        "support": support,
        "vectors": [{"N": N, "values": vec} for N, vec in zip(window, vectors)],
    }


def save_family_payload(path: Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("wb") as fh:
        pickle.dump(payload, fh, protocol=pickle.HIGHEST_PROTOCOL)


def load_basis_file(path: Path) -> BasisData:
    with path.open("rb") as fh:
        payload = pickle.load(fh)
    return BasisData(
        support=[int(t) for t in payload["support"]],
        basis=[[float(x) for x in vec] for vec in payload["basis"]],
        orthonormal=bool(payload.get("orthonormal", False)),
        label=payload.get("label"),
    )


def dot(u: list[float], v: list[float]) -> float:
    return sum(a * b for a, b in zip(u, v))


def vec_sub(u: list[float], v: list[float]) -> list[float]:
    return [a - b for a, b in zip(u, v)]


def vec_add_scaled(acc: list[float], scale: float, v: list[float]) -> None:
    for i, x in enumerate(v):
        acc[i] += scale * x


def solve_linear_system(a: list[list[float]], b: list[float]) -> list[float]:
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
            factor = aug[r][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                aug[r][j] -= factor * aug[col][j]
    return [aug[i][n] for i in range(n)]


def basis_projection(vector: list[float], basis: BasisData) -> tuple[list[float], list[float]]:
    if not basis.basis:
        zero = [0.0] * len(vector)
        return zero, vector[:]
    if basis.orthonormal:
        coeffs = [dot(v, vector) for v in basis.basis]
    else:
        gram = [[dot(u, v) for v in basis.basis] for u in basis.basis]
        rhs = [dot(v, vector) for v in basis.basis]
        coeffs = solve_linear_system(gram, rhs)
    approx = [0.0] * len(vector)
    for c, b in zip(coeffs, basis.basis):
        vec_add_scaled(approx, c, b)
    return approx, vec_sub(vector, approx)


def gram_schmidt_orthonormalize(vectors: list[list[float]]) -> list[list[float]]:
    out: list[list[float]] = []
    for vec in vectors:
        cur = vec[:]
        for b in out:
            coeff = dot(cur, b)
            for i, x in enumerate(b):
                cur[i] -= coeff * x
        norm_cur = math.sqrt(max(dot(cur, cur), 0.0))
        if norm_cur <= 1e-18:
            continue
        out.append([x / norm_cur for x in cur])
    return out


def basis_report(vectors: list[list[float]], basis: BasisData) -> Report:
    full = 0.0
    captured = 0.0
    shadow = 0.0
    for vec in vectors:
        full_slice = sum(vec)
        full_slice_energy = dot(vec, vec)
        approx, residual = basis_projection(vec, basis)
        captured_slice = dot(approx, approx)
        residual_slice_sum = sum(residual)
        full += full_slice_energy
        captured += captured_slice
        shadow += residual_slice_sum * residual_slice_sum
    return Report(
        full_family_energy=full,
        captured_family_energy=captured,
        residual_family_energy=full - captured,
        shadow_residual_energy=shadow,
    )


def leave_one_out_svd_entries(
    *,
    window: list[int],
    support: list[int],
    vectors: list[list[float]],
    rank: int,
    label_prefix: str,
) -> list[LeaveOneOutEntry]:
    entries: list[LeaveOneOutEntry] = []
    for held_out_idx, (held_out_N, held_out_vec) in enumerate(zip(window, vectors)):
        train_vectors = [vec for i, vec in enumerate(vectors) if i != held_out_idx]
        basis, _cumulative = svd_basis_from_family_vectors(
            support=support,
            vectors=train_vectors,
            rank=rank,
            label=f"{label_prefix}-loo-{held_out_N}",
        )
        approx, residual = basis_projection(held_out_vec, basis)
        captured = dot(approx, approx)
        residual_energy = dot(residual, residual)
        shadow = sum(residual) ** 2
        entries.append(
            LeaveOneOutEntry(
                held_out_index=held_out_idx,
                held_out_N=held_out_N,
                training_rank=len(basis.basis),
                captured_energy=captured,
                residual_energy=residual_energy,
                shadow_residual_energy=shadow,
            )
        )
    return entries


def gram_matrix(vectors: list[list[float]]) -> list[list[float]]:
    n = len(vectors)
    return [[dot(vectors[i], vectors[j]) for j in range(n)] for i in range(n)]


def jacobi_eigendecomposition_symmetric(
    a: list[list[float]],
    tol: float = 1e-18,
    max_sweeps: int = 100,
) -> tuple[list[float], list[list[float]]]:
    n = len(a)
    mat = [row[:] for row in a]
    vecs = [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]
    for _ in range(max_sweeps):
        p = 0
        q = 1 if n > 1 else 0
        max_val = 0.0
        for i in range(n):
            for j in range(i + 1, n):
                v = abs(mat[i][j])
                if v > max_val:
                    max_val = v
                    p, q = i, j
        if max_val < tol:
            break
        app = mat[p][p]
        aqq = mat[q][q]
        apq = mat[p][q]
        tau = (aqq - app) / (2.0 * apq)
        t = math.copysign(1.0 / (abs(tau) + math.sqrt(1.0 + tau * tau)), tau)
        c = 1.0 / math.sqrt(1.0 + t * t)
        s = t * c
        for k in range(n):
            if k != p and k != q:
                mkp = mat[k][p]
                mkq = mat[k][q]
                mat[k][p] = c * mkp - s * mkq
                mat[p][k] = mat[k][p]
                mat[k][q] = s * mkp + c * mkq
                mat[q][k] = mat[k][q]
        mat[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq
        mat[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq
        mat[p][q] = 0.0
        mat[q][p] = 0.0
        for k in range(n):
            vkp = vecs[k][p]
            vkq = vecs[k][q]
            vecs[k][p] = c * vkp - s * vkq
            vecs[k][q] = s * vkp + c * vkq
    eigvals = [mat[i][i] for i in range(n)]
    eigvecs = [[vecs[i][j] for i in range(n)] for j in range(n)]
    return eigvals, eigvecs


def svd_basis_from_family_vectors(
    support: list[int],
    vectors: list[list[float]],
    rank: int,
    label: str,
) -> tuple[BasisData, list[float]]:
    gram = gram_matrix(vectors)
    eigvals, eigvecs = jacobi_eigendecomposition_symmetric(gram)
    pairs = sorted(zip(eigvals, eigvecs), key=lambda x: x[0], reverse=True)
    total = sum(max(ev, 0.0) for ev, _ in pairs)
    top_ev = max((max(ev, 0.0) for ev, _ in pairs), default=0.0)
    ev_cut = top_ev * 1e-12
    cumulative: list[float] = []
    acc = 0.0
    for ev, _ in pairs:
        acc += max(ev, 0.0)
        cumulative.append(0.0 if total == 0.0 else acc / total)
    basis_vectors: list[list[float]] = []
    kept = 0
    for ev, coeffs in pairs:
        if kept >= rank:
            break
        if ev <= ev_cut:
            continue
        sigma = math.sqrt(ev)
        u = [0.0] * len(support)
        for c, vec in zip(coeffs, vectors):
            vec_add_scaled(u, c / sigma, vec)
        norm_u = math.sqrt(max(dot(u, u), 0.0))
        if norm_u <= 1e-18:
            continue
        basis_vectors.append([x / norm_u for x in u])
        kept += 1
    basis_vectors = gram_schmidt_orthonormalize(basis_vectors)
    basis = BasisData(
        support=support,
        basis=basis_vectors,
        orthonormal=True,
        label=label,
    )
    return basis, cumulative


def save_basis_file(path: Path, basis: BasisData) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "support": basis.support,
        "basis": basis.basis,
        "orthonormal": basis.orthonormal,
        "label": basis.label,
    }
    with path.open("wb") as fh:
        pickle.dump(payload, fh, protocol=pickle.HIGHEST_PROTOCOL)


def parse_mode_file(path: Path) -> list[int]:
    out: list[int] = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        out.append(int(line))
    return out


def parse_n_list(spec: str) -> list[int]:
    out: list[int] = []
    for piece in spec.split(","):
        piece = piece.strip()
        if not piece:
            continue
        out.append(int(piece))
    if not out:
        raise SystemExit("--N-list produced an empty window.")
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Exact-weight minor singularity harness on repo objects.")
    parser.add_argument("--X", type=int, required=True)
    parser.add_argument("--object", choices=["weighted", "centered", "coeffarith"], default="centered")
    parser.add_argument("--backend", choices=["exact", "hybrid"], default="exact")
    parser.add_argument("--qsplit", type=int, default=2000, help="Hybrid backend cutoff.")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--topK", type=int, default=20)
    parser.add_argument("--mode-file", type=Path, default=None, help="Optional ordered mode list file.")
    parser.add_argument("--basis-file", type=Path, default=None, help="Optional pickled low-rank basis file.")
    parser.add_argument(
        "--basis-template",
        choices=["alt-dct", "alt-harmonic"],
        default=None,
        help="Optional deterministic basis template evaluated directly on the exact family.",
    )
    parser.add_argument("--basis-rank", type=int, default=None, help="Rank for --basis-template.")
    parser.add_argument("--export-family", type=Path, default=None, help="Optional path to export the exact family matrix payload.")
    parser.add_argument("--svd-rank", type=int, default=None, help="Optional in-repo family-SVD rank for basis extraction.")
    parser.add_argument("--loo-svd-rank", type=int, default=None, help="Optional leave-one-out family-SVD rank evaluated on held-out slices.")
    parser.add_argument("--export-basis", type=Path, default=None, help="Optional path to export the in-repo SVD basis.")
    parser.add_argument("--window", choices=["five", "three"], default="five")
    parser.add_argument("--N-list", type=str, default=None, help="Optional explicit comma-separated window points, overriding --window.")
    args = parser.parse_args()

    X = args.X
    window = canonical_window_points(X) if args.window == "five" else [X, X + H // 2, X + H]
    if args.N_list is not None:
        window = parse_n_list(args.N_list)

    print("== Parameters ==")
    print(f"X={X:,}  object={args.object}  backend={args.backend}  topK={args.topK}  jobs={args.jobs}")
    print(f"window={window}")

    print("[build] precomputing exact arithmetic core by sum-level regrouping")
    by_s = sum_by_s(X)
    print(f"[build] distinct sum levels: {len(by_s):,}")

    required_abs_t = {0}
    for N in window:
        for s in by_s:
            required_abs_t.add(abs(s - N))
    required_abs_t = {t for t in required_abs_t if t <= X + H}
    if args.object == "coeffarith":
        required_abs_t = set(range(0, X + H + 1))
    print(f"[build] distinct |t| values needed for raw exact family: {len(required_abs_t):,}")

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
    wstats = weight_stats(X, weights) if args.object == "coeffarith" else None
    support, vectors = build_family_vectors(
        X=X,
        obj=args.object,
        slices=slices,
        weights=weights,
        wstats=wstats,
    )

    if args.export_family is not None:
        payload = export_family_payload(
            X=X,
            obj=args.object,
            window=window,
            support=support,
            vectors=vectors,
        )
        save_family_payload(args.export_family, payload)
        print(f"[export] wrote exact family payload to {args.export_family}")

    if args.basis_template is not None:
        if args.basis_rank is None or args.basis_rank <= 0:
            raise SystemExit("--basis-template requires --basis-rank >= 1")
        if args.basis_template == "alt-dct":
            basis = alternating_dct_basis(support=support, rank=args.basis_rank, orthonormalize=True)
        elif args.basis_template == "alt-harmonic":
            basis = alternating_harmonic_basis(support=support, rank=args.basis_rank, orthonormalize=True)
        else:
            raise SystemExit(f"unknown basis template: {args.basis_template}")
        print(
            f"[basis] built deterministic template {args.basis_template}"
            f" rank={args.basis_rank}"
            + (f" ({basis.label})" if basis.label else "")
        )
        if args.export_basis is not None:
            save_basis_file(args.export_basis, basis)
            print(f"[basis] wrote basis to {args.export_basis}")
        report = basis_report(vectors, basis)
        print("\n== Report ==")
        print(f"fullFamilyEnergy      = {report.full_family_energy:.12g}")
        print(f"capturedFamilyEnergy  = {report.captured_family_energy:.12g}")
        print(f"residualFamilyEnergy  = {report.residual_family_energy:.12g}")
        print(f"shadowResidualEnergy  = {report.shadow_residual_energy:.12g}")
        print(f"captureRatio          = {100.0 * report.capture_ratio:.6f}%")
        print(f"residualRatio         = {100.0 * report.residual_ratio:.6f}%")
        print(f"shadowResidualRatio   = {100.0 * report.shadow_residual_ratio:.6f}%")
        return

    if args.svd_rank is not None:
        basis, cumulative = svd_basis_from_family_vectors(
            support=support,
            vectors=vectors,
            rank=args.svd_rank,
            label=f"{args.object}-family-svd-X{X}-rank{args.svd_rank}",
        )
        print(
            "[svd] cumulative captures by rank: "
            + ", ".join(f"r={i+1}:{100.0*cumulative[i]:.4f}%" for i in range(min(len(cumulative), len(vectors))))
        )
        print(f"[svd] retained {len(basis.basis)} basis vectors")
        if args.export_basis is not None:
            save_basis_file(args.export_basis, basis)
            print(f"[svd] wrote orthonormal basis to {args.export_basis}")
        report = basis_report(vectors, basis)
        print("\n== Report ==")
        print(f"fullFamilyEnergy      = {report.full_family_energy:.12g}")
        print(f"capturedFamilyEnergy  = {report.captured_family_energy:.12g}")
        print(f"residualFamilyEnergy  = {report.residual_family_energy:.12g}")
        print(f"shadowResidualEnergy  = {report.shadow_residual_energy:.12g}")
        print(f"captureRatio          = {100.0 * report.capture_ratio:.6f}%")
        print(f"residualRatio         = {100.0 * report.residual_ratio:.6f}%")
        print(f"shadowResidualRatio   = {100.0 * report.shadow_residual_ratio:.6f}%")
        return

    if args.loo_svd_rank is not None:
        entries = leave_one_out_svd_entries(
            window=window,
            support=support,
            vectors=vectors,
            rank=args.loo_svd_rank,
            label_prefix=f"{args.object}-family-svd-X{X}-rank{args.loo_svd_rank}",
        )
        print("\n== Leave-One-Out Report ==")
        capture_avg = 0.0
        residual_avg = 0.0
        shadow_avg = 0.0
        for entry in entries:
            capture_avg += entry.capture_ratio
            residual_avg += entry.residual_ratio
            shadow_avg += entry.shadow_residual_ratio
            print(
                f"held_out_N={entry.held_out_N}"
                f" rank={entry.training_rank}"
                f" capture={100.0 * entry.capture_ratio:.6f}%"
                f" residual={100.0 * entry.residual_ratio:.6f}%"
                f" shadowResidual={100.0 * entry.shadow_residual_ratio:.6e}%"
            )
        m = float(len(entries))
        if m > 0:
            print("-- averages --")
            print(f"avgCaptureRatio        = {100.0 * capture_avg / m:.6f}%")
            print(f"avgResidualRatio       = {100.0 * residual_avg / m:.6f}%")
            print(f"avgShadowResidualRatio = {100.0 * shadow_avg / m:.6e}%")
        return

    if args.basis_file is not None:
        basis = load_basis_file(args.basis_file)
        if basis.support != support:
            raise SystemExit("Basis support does not match exact family support for this object/X/window.")
        print(
            f"[basis] loaded {len(basis.basis)} vectors"
            + (f" ({basis.label})" if basis.label else "")
            + f" from {args.basis_file}"
        )
        report = basis_report(vectors, basis)
        print("\n== Report ==")
        print(f"fullFamilyEnergy      = {report.full_family_energy:.12g}")
        print(f"capturedFamilyEnergy  = {report.captured_family_energy:.12g}")
        print(f"residualFamilyEnergy  = {report.residual_family_energy:.12g}")
        print(f"shadowResidualEnergy  = {report.shadow_residual_energy:.12g}")
        print(f"captureRatio          = {100.0 * report.capture_ratio:.6f}%")
        print(f"residualRatio         = {100.0 * report.residual_ratio:.6f}%")
        print(f"shadowResidualRatio   = {100.0 * report.shadow_residual_ratio:.6f}%")
        return

    if args.mode_file is not None:
        ordered_modes = parse_mode_file(args.mode_file)
        print(f"[modes] loaded {len(ordered_modes)} ordered modes from {args.mode_file}")
    else:
        if args.object == "weighted":
            ordered_modes = ordered_modes_from_energy(
                X=X,
                energy=weighted_mode_energies(slices),
                fill_base_modes=False,
            )
        elif args.object == "centered":
            energy, _base = centered_mode_energy_info(X, slices)
            ordered_modes = ordered_modes_from_energy(
                X=X,
                energy=energy,
                fill_base_modes=True,
            )
        else:
            assert wstats is not None
            energy = coeffarith_mode_energy_info(X, slices, weights, wstats)
            ordered_modes = ordered_modes_from_energy(
                X=X,
                energy=energy,
                fill_base_modes=False,
            )
        print(f"[modes] generated energy-ranked mode order of length {len(ordered_modes):,}")

    selected = set(ordered_modes[: args.topK])
    print(f"[modes] selected top-{args.topK}: {ordered_modes[:args.topK]}")

    if args.object == "weighted":
        report = weighted_report(X, slices, selected)
    elif args.object == "centered":
        report = centered_report(X, slices, selected)
    else:
        assert wstats is not None
        report = coeffarith_report(X, slices, weights, wstats, selected)

    print("\n== Report ==")
    print(f"fullFamilyEnergy      = {report.full_family_energy:.12g}")
    print(f"capturedFamilyEnergy  = {report.captured_family_energy:.12g}")
    print(f"residualFamilyEnergy  = {report.residual_family_energy:.12g}")
    print(f"shadowResidualEnergy  = {report.shadow_residual_energy:.12g}")
    print(f"captureRatio          = {100.0 * report.capture_ratio:.6f}%")
    print(f"residualRatio         = {100.0 * report.residual_ratio:.6f}%")
    print(f"shadowResidualRatio   = {100.0 * report.shadow_residual_ratio:.6f}%")


if __name__ == "__main__":
    main()
