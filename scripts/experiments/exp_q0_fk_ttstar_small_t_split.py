#!/usr/bin/env python3
"""
Experiment (Step5): small-|t| split for the TT*/Toeplitz coefficients F_k.

We study whether |F_k|^2 (and the implied M2 scale) is dominated by terms with
small |t|, where

  t = |2n + k - N|.

For each sampled k>0 we compute:
  - F_k(full) via Monte Carlo (same estimator as exp_q0_fk_ttstar_w_hat_mc.py),
  - F_k(|t|≤T) exactly for a list of T values, by enumerating the at-most-two
    n solutions for each t (since 2n+k-N = ±t).

This is NOT a proof and does NOT generate a Lean certificate. It is designed to
guide a certifiable split U = U_small(T) + U_tail(T).

Kernel:
  Uses the same hybrid hard-arc kernel approximation W_hat_hybrid(t) from
  exp_q0_fk_ttstar_w_hat_mc.py.

Constant mode t=0:
  For the balanced/mean-zero α-weight, the t=0 Fourier mode is removed. The
  existing Monte Carlo script implicitly uses W(0)=0 by defining W_hat only for
  t>0. We keep that behavior by default.
  You can include an explicit unbalanced W(0)=meas(MA) via --use-w0.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
import time
from array import array
from pathlib import Path

from exp_q0_fk_ttstar_w_hat_mc import (
    compute_S_all,
    estimate_Fk_mc,
    mobius_phi_sieve,
    mobius_sieve,
    parse_quantiles,
    quantile,
    von_mangoldt_array,
    w_hat_hybrid,
)


def parse_int_list(path: Path) -> list[int]:
    out: list[int] = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        out.append(int(line))
    return out


def parse_k_list(s: str) -> list[int]:
    """
    Comma-separated integers, plus optional ranges a:b:c (inclusive).
    """
    out: list[int] = []
    for part in s.split(","):
        part = part.strip()
        if not part:
            continue
        if ":" in part:
            a_s, b_s, c_s = (x.strip() for x in part.split(":"))
            a = int(a_s)
            b = int(b_s)
            c = int(c_s)
            if c == 0:
                raise ValueError("range step must be nonzero")
            if (b - a) * c < 0:
                raise ValueError("range step has wrong sign")
            x = a
            while (x <= b) if c > 0 else (x >= b):
                out.append(x)
                x += c
        else:
            out.append(int(part))
    return out


def meas_major_arcs_hard(*, X: int, Q0: int) -> float:
    """
    meas(MA_Q0(X)) for disjoint hard arcs:
      Σ_{q≤Q0} φ(q) * (2/(qX)).
    We compute φ up to Q0 exactly by sieve.
    """
    _, phi = mobius_phi_sieve(Q0)
    acc = 0.0
    for q in range(1, Q0 + 1):
        acc += phi[q] / q
    return (2.0 / X) * acc


def fk_small_exact_prefix(
    *,
    lam: array,
    w_cache: dict[int, float],
    X: int,
    Q0: int,
    Qsplit: int,
    mu: list[int],
    phi: list[int],
    s_q0: array,
    s_qs: array,
    N: int,
    k: int,
    T_list: list[int],
    Tmax: int,
    w0: float,
) -> list[float]:
    """
    Return [F_k(|t|≤T)] for each T in T_list (assumed sorted, T<=Tmax).
    """
    n_hi = N - 2 - k
    if n_hi < 2:
        return [0.0 for _ in T_list]
    n_lo = 2

    out = [0.0 for _ in T_list]
    ti = 0
    acc = 0.0

    # Precompute (N-k) parity: t must have same parity as (N-k) for n to be integral.
    nk = N - k

    for t in range(0, Tmax + 1):
        if (nk + t) & 1:
            continue

        w = 0.0
        if t == 0:
            w = w0
        else:
            w = w_cache.get(t)
            if w is None:
                w = w_hat_hybrid(X=X, Q0=Q0, Qsplit=Qsplit, t=t, mu=mu, phi=phi, s_q0=s_q0, s_qs=s_qs)
                w_cache[t] = w

        # Solutions: n = (N - k ± t)/2.
        # For t=0, this is a single solution.
        n1 = (nk + t) // 2
        if n_lo <= n1 <= n_hi:
            a = lam[n1]
            b = lam[n1 + k]
            if a and b:
                acc += a * b * w
        if t != 0:
            n2 = (nk - t) // 2
            if n_lo <= n2 <= n_hi:
                a = lam[n2]
                b = lam[n2 + k]
                if a and b:
                    acc += a * b * w

        while ti < len(T_list) and t == T_list[ti]:
            out[ti] = acc
            ti += 1
    # Fill any remaining (should not happen if Tmax >= max T).
    while ti < len(T_list):
        out[ti] = acc
        ti += 1
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description="Experiment: small-|t| split for F_k.")
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--Q0", type=int, default=30_000)
    ap.add_argument("--Qsplit", type=int, default=500)
    ap.add_argument("--H", type=int, default=10_000, help="Default N=X+H unless overridden.")
    ap.add_argument("--N", type=int, default=None)
    ap.add_argument("--Tmax", type=int, default=2_000_000, help="S_Q precompute limit (default 2*X).")
    ap.add_argument("--T-list", type=str, default="0,10,100,1000,10000", help="Comma list of T cutoffs.")
    ap.add_argument("--k-samples", type=int, default=200, help="Number of random k samples.")
    ap.add_argument("--n-samples", type=int, default=5000, help="MC n samples per k for F_k(full).")
    ap.add_argument("--seed", type=int, default=40)
    ap.add_argument("--include-structured", action="store_true", help="Add k near 30k*m clusters.")
    ap.add_argument("--k-file", type=str, default=None, help="Optional file with explicit k values.")
    ap.add_argument("--k-list", type=str, default=None, help="Optional explicit k values (comma list; supports a:b:c).")
    ap.add_argument("--quantiles", type=str, default="0.5,0.9,0.99,0.999", help="Quantiles for ratios.")
    ap.add_argument("--use-w0", action="store_true", help="Include unbalanced constant mode W(0)=meas(MA).")
    args = ap.parse_args()

    X = args.X
    Q0 = args.Q0
    Qsplit = args.Qsplit
    H = args.H
    N = args.N if args.N is not None else X + H
    Tmax = args.Tmax if args.Tmax is not None else 2 * X
    rng = random.Random(args.seed)

    t_list = [int(x.strip()) for x in args.T_list.split(",") if x.strip()]
    if not t_list:
        raise ValueError("empty --T-list")
    t_list = sorted(set(t_list))
    if t_list[0] < 0:
        raise ValueError("T cutoffs must be nonnegative")
    Tmax_small = t_list[-1]

    qs = parse_quantiles(args.quantiles)

    print("== Parameters ==")
    print(
        f"X={X:,}  Q0={Q0:,}  Qsplit={Qsplit:,}  N={N:,}  Tmax={Tmax:,}  "
        f"k_samples={args.k_samples:,}  n_samples={args.n_samples:,}  seed={args.seed}"
    )
    print(f"T cutoffs: {t_list}")
    print(f"use_w0={args.use_w0}")

    t0 = time.time()
    mu, phi = mobius_phi_sieve(Qsplit)
    print(f"[time] sieve(mu,phi) to Qsplit: {time.time()-t0:.3f}s")

    t1 = time.time()
    mu_q0 = mobius_sieve(Q0)
    print(f"[time] sieve(mu) Q0/Qsplit:     {time.time()-t1:.3f}s")

    t2 = time.time()
    s_q0 = compute_S_all(Q=Q0, Tmax=Tmax, mu=mu_q0)
    print(f"[time] S_Q0(t) to Tmax:         {time.time()-t2:.3f}s")

    t3 = time.time()
    s_qs = compute_S_all(Q=Qsplit, Tmax=Tmax, mu=mu_q0)
    print(f"[time] S_Qsplit(t) to Tmax:     {time.time()-t3:.3f}s")

    # Extend phi to Q0 for Ramanujan sums in w_hat_hybrid (needs phi[q],phi[h] for q<=Qsplit only).
    # For q<=Qsplit we already computed phi; for h<=Qsplit too. So OK.
    # But we need mu up to Qsplit as well. mu already OK.

    t4 = time.time()
    lam = von_mangoldt_array(N)
    print(f"[time] Λ array to N:            {time.time()-t4:.3f}s")

    # Build k list
    k_set: set[int] = set()
    if args.k_file:
        k_set.update(parse_int_list(Path(args.k_file)))
    if args.k_list:
        k_set.update(parse_k_list(args.k_list))
    if args.k_samples > 0:
        for _ in range(args.k_samples):
            # k ∈ [1, N-4] so that n∈[2,N-2-k] can be nonempty.
            k_set.add(rng.randrange(1, max(2, N - 3)))
    if args.include_structured:
        for m in range(1, 34):
            base = 30_000 * m
            for off in range(-1000, 1001, 200):
                k_set.add(base + off)

    # Filter admissible k
    k_list = sorted(k for k in k_set if 1 <= k <= (N - 4))
    if not k_list:
        raise ValueError("no admissible k values")

    w0 = 0.0
    if args.use_w0:
        w0 = meas_major_arcs_hard(X=X, Q0=Q0)
    print(f"k count: {len(k_list)}  (min={k_list[0]}, max={k_list[-1]})")
    if args.use_w0:
        print(f"W(0)=meas(MA)≈{w0:.6e}")

    # Shared kernel cache
    w_cache: dict[int, float] = {}

    # Compute F0(full) by MC (optional always, to get a consistent M2_est formula).
    t5 = time.time()
    f0_full = estimate_Fk_mc(
        rng=rng,
        lam=lam,
        w_cache=w_cache,
        X=X,
        Q0=Q0,
        Qsplit=Qsplit,
        mu=mu,
        phi=phi,
        s_q0=s_q0,
        s_qs=s_qs,
        N=N,
        k=0,
        n_samples=args.n_samples,
    )
    print(f"F_0(full, MC): {f0_full:.6e}  |F_0|^2: {f0_full*f0_full:.6e}  [time {time.time()-t5:.3f}s]")

    # Compute F0 small exact for each T (use same formula; k=0 is allowed).
    f0_small_by_T = fk_small_exact_prefix(
        lam=lam,
        w_cache=w_cache,
        X=X,
        Q0=Q0,
        Qsplit=Qsplit,
        mu=mu,
        phi=phi,
        s_q0=s_q0,
        s_qs=s_qs,
        N=N,
        k=0,
        T_list=t_list,
        Tmax=Tmax_small,
        w0=w0,
    )

    # Per-k arrays
    fk_full: list[float] = []
    fk_full_sq: list[float] = []
    fk_small_by_T: list[list[float]] = [[] for _ in t_list]
    fk_small_sq_by_T: list[list[float]] = [[] for _ in t_list]
    ratio_sq_by_T: list[list[float]] = [[] for _ in t_list]  # |F_small|^2 / |F_full|^2 when full>0

    t6 = time.time()
    for k in k_list:
        f_full = estimate_Fk_mc(
            rng=rng,
            lam=lam,
            w_cache=w_cache,
            X=X,
            Q0=Q0,
            Qsplit=Qsplit,
            mu=mu,
            phi=phi,
            s_q0=s_q0,
            s_qs=s_qs,
            N=N,
            k=k,
            n_samples=args.n_samples,
        )
        fk_full.append(f_full)
        full_sq = f_full * f_full
        fk_full_sq.append(full_sq)

        f_small_list = fk_small_exact_prefix(
            lam=lam,
            w_cache=w_cache,
            X=X,
            Q0=Q0,
            Qsplit=Qsplit,
            mu=mu,
            phi=phi,
            s_q0=s_q0,
            s_qs=s_qs,
            N=N,
            k=k,
            T_list=t_list,
            Tmax=Tmax_small,
            w0=w0,
        )
        for i, f_small in enumerate(f_small_list):
            fk_small_by_T[i].append(f_small)
            s_sq = f_small * f_small
            fk_small_sq_by_T[i].append(s_sq)
            if full_sq > 0.0:
                ratio_sq_by_T[i].append(s_sq / full_sq)
    print(f"[time] computed {len(k_list)} k values (MC full + exact small-t): {time.time()-t6:.3f}s")
    print(f"kernel cache size: {len(w_cache):,} distinct t values")

    # Full stats
    mean_full_sq = statistics.mean(fk_full_sq)
    med_full_sq = statistics.median(fk_full_sq)
    max_full = max(abs(x) for x in fk_full)

    max_k_support = N - 4  # k>0 support size in the project
    m2_full_est = math.sqrt((f0_full * f0_full) + 2.0 * max_k_support * mean_full_sq)

    print("\n== Full (MC) stats over k>0 ==")
    print(f"mean |F_k(full)|^2:   {mean_full_sq:.6e}")
    print(f"median |F_k(full)|^2: {med_full_sq:.6e}")
    print(f"max |F_k(full)|:      {max_full:.6e}")
    print(f"M2_full_est ≈ {m2_full_est:,.1f}")

    # Small-t split stats for each T
    print("\n== Small-|t| split ==")
    for i, T in enumerate(t_list):
        mean_small_sq = statistics.mean(fk_small_sq_by_T[i])
        med_small_sq = statistics.median(fk_small_sq_by_T[i])
        max_small = max(abs(x) for x in fk_small_by_T[i])
        share_energy = (sum(fk_small_sq_by_T[i]) / sum(fk_full_sq)) if sum(fk_full_sq) > 0.0 else float("nan")

        f0_small = f0_small_by_T[i]
        m2_small_est = math.sqrt((f0_small * f0_small) + 2.0 * max_k_support * mean_small_sq)

        ratios = ratio_sq_by_T[i]
        r_mean = statistics.mean(ratios) if ratios else float("nan")
        r_med = statistics.median(ratios) if ratios else float("nan")
        r_max = max(ratios) if ratios else float("nan")

        print(f"\nT={T}:")
        print(f"  mean |F_k(|t|≤T)|^2:   {mean_small_sq:.6e}")
        print(f"  median |F_k(|t|≤T)|^2: {med_small_sq:.6e}")
        print(f"  max |F_k(|t|≤T)|:      {max_small:.6e}")
        print(f"  energy share Σ|F_small|^2 / Σ|F_full|^2: {share_energy:.6e}")
        print(f"  M2_small_est ≈ {m2_small_est:,.1f}")
        print(f"  ratios r=|F_small|^2/|F_full|^2 over sampled k: mean={r_mean:.3e} med={r_med:.3e} max={r_max:.3e}")
        if qs:
            print("  ratio quantiles:")
            for q in qs:
                print(f"    q={q:>7}: {quantile(ratios, q):.6e}")


if __name__ == "__main__":
    main()

