#!/usr/bin/env python3
"""
Experiment: estimate the TT*/Parseval scale by sampling the linearized Toeplitz coefficients F_k.

This uses the same linearized hard-arc kernel as exp_q0_fk_ttstar_linearized.py:
  W_lin(t) := (2/X) * S(t),  S(t) = Σ_{q≤Q0} c_q(t)/q,
computed via the divisor/Mertens-weighted identity.

We compute (heuristic):
  F_k ≈ Σ_{n=2}^{N-2-k} Λ(n) Λ(n+k) * W_lin(|2n+k-N|).

Then we report:
  - statistics of |F_k| and |F_k|^2 over sampled k,
  - an extrapolated M2 estimate:
      M2_est ≈ sqrt( Σ_{k∈[-N,N]} |F_k|^2 )
    using symmetry and the sampled mean of |F_k|^2 for k>0.

This is NOT a proof and does NOT generate a Lean certificate.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
import time
from array import array


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


def mertens_weighted(mu: list[int]) -> list[float]:
    m = [0.0] * len(mu)
    acc = 0.0
    for n in range(1, len(mu)):
        acc += mu[n] / n
        m[n] = acc
    return m


def compute_S(*, Q0: int, Tmax: int, mu: list[int]) -> array:
    """
    S(t) = Σ_{q≤Q0} c_q(t)/q via:
      Σ_{q≤Q0} c_q(t)/q = Σ_{d|t, d≤Q0} M(⌊Q0/d⌋).
    """
    m = mertens_weighted(mu)
    s_arr = array("d", [0.0]) * (Tmax + 1)
    max_d = min(Q0, Tmax)
    for d in range(1, max_d + 1):
        coef = m[Q0 // d]
        for t in range(d, Tmax + 1, d):
            s_arr[t] += coef
    return s_arr


def von_mangoldt_array(n: int) -> array:
    lam = array("d", [0.0]) * (n + 1)
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    limit = int(math.isqrt(n))
    for p in range(2, limit + 1):
        if sieve[p]:
            start = p * p
            sieve[start : n + 1 : p] = b"\x00" * (((n - start) // p) + 1)
    primes = [i for i in range(2, n + 1) if sieve[i]]
    for p in primes:
        lp = math.log(p)
        pk = p
        while pk <= n:
            lam[pk] = lp
            pk *= p
    return lam


def compute_Fk(*, lam: array, wlin: array, N: int, k: int) -> float:
    if k < 0:
        raise ValueError("k must be nonnegative")
    n_hi = N - 2 - k
    if n_hi < 2:
        return 0.0
    s = 0.0
    lam_local = lam
    w_local = wlin
    N_local = N
    kk = k
    for n in range(2, n_hi + 1):
        a = lam_local[n]
        if a == 0.0:
            continue
        b = lam_local[n + kk]
        if b == 0.0:
            continue
        t = (2 * n + kk) - N_local
        if t < 0:
            t = -t
        s += a * b * w_local[t]
    return s


def main() -> None:
    parser = argparse.ArgumentParser(description="Experiment: sample F_k via W_lin and estimate M2.")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--H", type=int, default=10_000, help="Default N=X+H unless overridden.")
    parser.add_argument("--N", type=int, default=None)
    parser.add_argument("--Tmax", type=int, default=None, help="Kernel t-range (default: 2*X).")
    parser.add_argument("--samples", type=int, default=300, help="Number of random k samples (k>0).")
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--max-k", type=int, default=None, help="Sample k uniformly in [1,max-k] (default N).")
    parser.add_argument("--include-structured", action="store_true", help="Also sample k near 30k*m clusters.")
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    N = (X + args.H) if args.N is None else args.N
    Tmax = (2 * X) if args.Tmax is None else args.Tmax
    max_k = N if args.max_k is None else args.max_k

    if X <= 0 or Q0 <= 0 or N <= 0 or Tmax <= 0:
        raise SystemExit("Require X,Q0,N,Tmax positive.")
    if max_k <= 0:
        raise SystemExit("Require max-k positive.")
    if args.samples <= 0:
        raise SystemExit("Require --samples > 0.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  N={N:,}  Tmax={Tmax:,}  samples={args.samples}  seed={args.seed}  max_k={max_k:,}")
    print(f"include_structured={args.include_structured}")

    t0 = time.perf_counter()
    mu = mobius_sieve(Q0)
    t1 = time.perf_counter()
    s_arr = compute_S(Q0=Q0, Tmax=Tmax, mu=mu)
    t2 = time.perf_counter()
    wlin = array("d", [0.0]) * (Tmax + 1)
    scale = 2.0 / X
    for t in range(1, Tmax + 1):
        wlin[t] = scale * s_arr[t]
    t3 = time.perf_counter()
    lam = von_mangoldt_array(N)
    t4 = time.perf_counter()
    print(f"[time] mu sieve:           {t1 - t0:.3f}s")
    print(f"[time] S(t) divisor-sieve: {t2 - t1:.3f}s")
    print(f"[time] W_lin build:        {t3 - t2:.3f}s")
    print(f"[time] Λ array to N:       {t4 - t3:.3f}s")

    rng = random.Random(args.seed)

    ks: list[int] = []
    # random k>0
    for _ in range(args.samples):
        ks.append(rng.randrange(1, max_k + 1))
    if args.include_structured:
        for base in [30_000, 60_000, 90_000, 120_000, 150_000, 180_000]:
            for off in [0, 200, 400, 600, 800, 1000]:
                k = base + off
                if 1 <= k <= max_k:
                    ks.append(k)

    # compute F0 separately (often the largest)
    t5 = time.perf_counter()
    f0 = compute_Fk(lam=lam, wlin=wlin, N=N, k=0)
    t6 = time.perf_counter()
    print(f"\nF_0: {f0:.6e}  |F_0|^2: {abs(f0)**2:.6e}  [time {t6 - t5:.3f}s]")

    abs_sq: list[float] = []
    abs_vals: list[float] = []
    max_abs = 0.0
    max_k_seen = 0
    t7 = time.perf_counter()
    for k in ks:
        fk = compute_Fk(lam=lam, wlin=wlin, N=N, k=k)
        afk = abs(fk)
        abs_vals.append(afk)
        abs_sq.append(afk * afk)
        if afk > max_abs:
            max_abs = afk
            max_k_seen = k
    t8 = time.perf_counter()
    print(f"[time] computed {len(ks)} F_k (k>0 samples): {t8 - t7:.3f}s")

    mean_sq = statistics.mean(abs_sq)
    med_sq = statistics.median(abs_sq)
    mean_abs = statistics.mean(abs_vals)
    med_abs = statistics.median(abs_vals)

    print("\n== Sample stats over k>0 ==")
    print(f"count:                      {len(ks)}")
    print(f"max |F_k|:                  {max_abs:.6e} at k={max_k_seen}")
    print(f"mean |F_k|:                 {mean_abs:.6e}")
    print(f"median |F_k|:               {med_abs:.6e}")
    print(f"mean |F_k|^2:               {mean_sq:.6e}")
    print(f"median |F_k|^2:             {med_sq:.6e}")

    # Extrapolate to full support k∈[-N,N] using symmetry:
    #   Σ_{k=-N}^N |F_k|^2 ≈ |F_0|^2 + 2 * Σ_{k=1}^N |F_k|^2
    # and approximate Σ_{k=1}^N |F_k|^2 ≈ N * mean_{sample} |F_k|^2.
    sum_sq_est = abs(f0) ** 2 + 2.0 * (N * mean_sq)
    m2_est = math.sqrt(sum_sq_est)
    print("\n== Extrapolated TT* scale (heuristic) ==")
    print(f"Σ_{'{'}k=-N..N{'}'} |F_k|^2  ≈  {sum_sq_est:.6e}")
    print(f"M2_est := sqrt(Σ|F_k|^2) ≈  {m2_est:.3f}")
    print("\nNOTE: Uses W_lin (not true W_hat) and treats sampled k as representative.")


if __name__ == "__main__":
    main()

