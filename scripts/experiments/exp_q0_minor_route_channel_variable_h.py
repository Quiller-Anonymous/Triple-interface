#!/usr/bin/env python3
"""
Variable-H route-channel feasibility study.

This is intentionally off the exact pinned repo surface. Its purpose is to reconcile
the exact fixed-`H = 10000` channel audit with the earlier Route-B style scaling studies
that used varying `H`.

Current supported regime:
  - `cube`: H = round(X^(1/3)), Q = round(H^0.4)

It computes the same route-facing slice-sum channels as the exact fixed-H scripts:
  weighted_total
  zero_mode
  mean_channel
  coeffarith

and compares them to the Route-B style scale
  H/X + 1/(H*Q^2).
"""

from __future__ import annotations

import argparse
import math
import multiprocessing as mp
import pickle
from bisect import bisect_left, bisect_right
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


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


def q0_norm_factor(N: int) -> float:
    return (1.0 / 800.0) * (1.0 / (math.log(N) ** 2))


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


@dataclass
class Params:
    X: int
    H: int
    Q: int
    Ucut: int


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
    norm_sq_centered: float


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
    return [int(piece.strip()) for piece in spec.split(",") if piece.strip()]


def fit_loglog_exponent(xs: list[int], ys: list[float]) -> float:
    pairs = [(x, y) for x, y in zip(xs, ys) if y > 0.0]
    if len(pairs) < 2:
        return float("nan")
    lx = [math.log(float(x)) for x, _ in pairs]
    ly = [math.log(float(y)) for _, y in pairs]
    mx = sum(lx) / len(lx)
    my = sum(ly) / len(ly)
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    den = sum((a - mx) * (a - mx) for a in lx)
    return num / den


def cube_params(X: int) -> Params:
    H = max(10, int(round(X ** (1.0 / 3.0))))
    Q = max(2, int(round(H ** 0.4)))
    Ucut = H + (H + 99) // 100
    return Params(X=X, H=H, Q=Q, Ucut=Ucut)


def prime_window_payload(p: Params) -> list[tuple[int, float]]:
    lo = p.X // 2 - p.H
    hi = p.X // 2 + p.H
    if lo < 2:
        lo = 2
    is_prime = sieve_primes_mask(hi)
    w_scale = 1.0 / (math.log(p.X) * (2 * p.H + 1))
    return [(n, w_scale * math.log(n)) for n in range(lo, hi + 1) if is_prime[n]]


def k_full_on_sbg(k: int, p: Params) -> float:
    if abs(k) > p.H:
        return 0.0
    return max(1.0 - (abs(k) / float(p.Ucut)), 0.0) / float(p.Ucut)


def major_zero_mode(p: Params, phi: list[int]) -> float:
    return (1.0 / p.X) + (2.0 / p.X) * sum(phi[q] / q for q in range(2, p.Q + 1))


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def major_w_hat_exact(p: Params, t: int, mu: list[int], phi: list[int]) -> float:
    s = 0.0
    two_pi_t_over_x = 2.0 * math.pi * t / p.X
    for q in range(1, p.Q + 1):
        cq = ramanujan_sum(q, t, mu, phi)
        if cq:
            s += cq * math.sin(two_pi_t_over_x / q)
    return s / (math.pi * t)


def minor_weight(p: Params, t: int, mu: list[int], phi: list[int]) -> float:
    if t == 0:
        return 1.0 - major_zero_mode(p, phi)
    return -major_w_hat_exact(p, abs(t), mu, phi)


def cache_path(p: Params) -> Path:
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    return CACHE_DIR / f"minor_weight_varH_X{p.X}_H{p.H}_Q{p.Q}.pkl"


def load_cache(path: Path) -> dict[int, float]:
    if not path.exists():
        return {}
    with path.open("rb") as fh:
        return pickle.load(fh)


def save_cache(path: Path, cache: dict[int, float]) -> None:
    with path.open("wb") as fh:
        pickle.dump(cache, fh, protocol=pickle.HIGHEST_PROTOCOL)


_WORKER = None


def _init_worker(payload):
    global _WORKER
    _WORKER = payload


def _worker_weight(t: int) -> tuple[int, float]:
    p, mu, phi = _WORKER
    return t, minor_weight(p, t, mu, phi)


def ensure_weights(p: Params, jobs: int) -> dict[int, float]:
    path = cache_path(p)
    cache = load_cache(path)
    needed = list(range(0, p.X + p.H + 1))
    missing = [t for t in needed if t not in cache]
    if not missing:
        return cache
    mu, phi = mobius_phi_sieve(p.Q)
    print(f"[weights] X={p.X:,} H={p.H} Q={p.Q} missing={len(missing):,}")
    if jobs <= 1:
        for i, t in enumerate(missing, start=1):
            cache[t] = minor_weight(p, t, mu, phi)
            if i % 500 == 0 or i == len(missing):
                save_cache(path, cache)
        return cache
    with mp.Pool(processes=jobs, initializer=_init_worker, initargs=((p, mu, phi),)) as pool:
        for i, (t, wt) in enumerate(pool.imap_unordered(_worker_weight, missing), start=1):
            cache[t] = wt
            if i % 500 == 0 or i == len(missing):
                save_cache(path, cache)
    return cache


def canonical_window_points(p: Params) -> list[int]:
    return [p.X, p.X + p.H // 4, p.X + p.H // 2, p.X + (3 * p.H) // 4, p.X + p.H]


def sum_by_s(p: Params) -> dict[int, float]:
    payload = prime_window_payload(p)
    primes = [n for n, _ in payload]
    vals = [a for _, a in payload]
    out: dict[int, float] = {}
    for i, n in enumerate(primes):
        lo = bisect_left(primes, n - p.H)
        hi = bisect_right(primes, n + p.H)
        ai = vals[i]
        for j in range(lo, hi):
            m = primes[j]
            contrib = ai * vals[j] * k_full_on_sbg(m - n, p)
            if contrib == 0.0:
                continue
            s = n + m
            out[s] = out.get(s, 0.0) + contrib
    return out


def build_weighted_slices(p: Params, window: list[int], weights: dict[int, float], by_s: dict[int, float]) -> list[SliceData]:
    m_nonzero = 2 * (p.X + p.H)
    s_items = list(by_s.items())
    out: list[SliceData] = []
    for N in window:
        q0 = q0_norm_factor(N)
        raw0 = q0 * by_s.get(N, 0.0) * weights[0]
        raw_nonzero: dict[int, float] = {}
        nonzero_sum = 0.0
        for s, core in s_items:
            t = s - N
            if t == 0:
                continue
            val = q0 * core * weights[abs(t)]
            if val != 0.0:
                raw_nonzero[t] = val
                nonzero_sum += val
        mean_nonzero = nonzero_sum / m_nonzero
        out.append(SliceData(N=N, raw0=raw0, raw_nonzero=raw_nonzero, nonzero_sum=nonzero_sum, mean_nonzero=mean_nonzero))
    return out


def weight_stats(p: Params, weights: dict[int, float]) -> WeightStats:
    ambient_max = p.X + p.H
    m_nonzero = 2 * ambient_max
    sum_pos = sum(weights[k] for k in range(1, ambient_max + 1))
    mean_nonzero = (2.0 * sum_pos) / m_nonzero
    sum_sq_pos = sum((weights[k] - mean_nonzero) ** 2 for k in range(1, ambient_max + 1))
    norm_sq_centered = 2.0 * sum_sq_pos
    return WeightStats(
        ambient_max=ambient_max,
        m_nonzero=m_nonzero,
        mean_nonzero=mean_nonzero,
        norm_sq_centered=norm_sq_centered,
    )


def coeffarith_alpha(sl: SliceData, ws: WeightStats, weights: dict[int, float]) -> float:
    numer = 0.0
    for t, raw in sl.raw_nonzero.items():
        numer += raw * (weights[abs(t)] - ws.mean_nonzero)
    numer -= sl.mean_nonzero * math.fsum((weights[abs(t)] - ws.mean_nonzero) for t in sl.raw_nonzero)
    if ws.norm_sq_centered == 0.0:
        return 0.0
    return numer / ws.norm_sq_centered


def route_bound(p: Params) -> float:
    return p.H / p.X + 1.0 / (p.H * (p.Q ** 2))


def main() -> None:
    parser = argparse.ArgumentParser(description="Variable-H route-channel feasibility study.")
    parser.add_argument("--X-list", type=str, default="10000,30000,100000,300000,1000000")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--regime", choices=["cube"], default="cube")
    args = parser.parse_args()

    xs = parse_x_list(args.X_list)
    rows: dict[str, list[tuple[int, float]]] = {
        "weighted_total": [],
        "zero_mode": [],
        "mean_channel": [],
        "coeffarith": [],
    }

    for X in xs:
        p = cube_params(X)
        print(f"== X={p.X:,} H={p.H} Q={p.Q} ==")
        by_s = sum_by_s(p)
        weights = ensure_weights(p, max(1, args.jobs))
        window = canonical_window_points(p)
        slices = build_weighted_slices(p, window, weights, by_s)
        ws = weight_stats(p, weights)

        weighted_sums: list[float] = []
        zero_sums: list[float] = []
        mean_sums: list[float] = []
        coeffarith_sums: list[float] = []

        ambient_support = [t for t in range(-(p.X + p.H), p.X + p.H + 1) if t != 0]
        weight_centered = {t: weights[abs(t)] - ws.mean_nonzero for t in ambient_support}

        for sl in slices:
            weighted_sums.append(sl.raw0 + sl.nonzero_sum)
            zero_sums.append(sl.raw0)
            mean_sums.append(sl.mean_nonzero * len(ambient_support))
            alpha = coeffarith_alpha(sl, ws, weights)
            coeff_sum = 0.0
            for t in ambient_support:
                raw = sl.raw_nonzero.get(t, 0.0)
                coeff_sum += (raw - sl.mean_nonzero) - alpha * weight_centered[t]
            coeffarith_sums.append(coeff_sum)

        stats = {
            "weighted_total": ChannelStats(weighted_sums),
            "zero_mode": ChannelStats(zero_sums),
            "mean_channel": ChannelStats(mean_sums),
            "coeffarith": ChannelStats(coeffarith_sums),
        }
        bnd = route_bound(p)
        print(f"route_bound={bnd:.12e}")
        for label, st in stats.items():
            ratio = st.energy / bnd
            rows[label].append((X, ratio))
            print(f"{label:14s} energy={st.energy:.12e} ratio={ratio:.12e}")
        print()

    print("== Ratio Exponents (energy / route_bound) ==")
    for label, vals in rows.items():
        xs2 = [x for x, _ in vals]
        ys = [y for _, y in vals]
        print(f"{label:14s} exponent={fit_loglog_exponent(xs2, ys):.6f}")


if __name__ == "__main__":
    main()
