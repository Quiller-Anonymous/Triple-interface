#!/usr/bin/env python3
"""
Experiment: probe the TT*/Toeplitz coefficients F_k using the linearized hard-arc kernel W_lin.

This is NOT a proof and does NOT generate a Lean certificate.

We use the (heuristic) linearized kernel:
  W_lin(t) := (2/X) * S(t),  where S(t) = Σ_{q≤Q0} c_q(t)/q
and S(t) is computed fast via the divisor/Mertens-weighted identity (same as exp_q0_wlin_ttstar_feasibility.py).

We then compute, for selected k≥0:
  F_k ≈ Σ_{n=2}^{N-2-k} Λ(n) Λ(n+k) * W_lin(|2n+k-N|).

This probes:
  - typical magnitude of F_k for various k,
  - whether there are obvious resonance spikes in k,
  - rough scale of partial ∑ |F_k|^2 over tested k.

Notes:
  - The true hard-arc kernel uses sin(2π t/(qX)) / (π t) instead of the linearized 2/(qX) factor.
  - Empirically, for worst structured t, |W_hat|/|W_lin| is ~0.8–0.85; this script reports W_lin only.
"""

from __future__ import annotations

import argparse
import math
import time
from array import array


def mobius_sieve(n: int) -> list[int]:
    """Return mu for 0..n via a linear sieve."""
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
    """M(u) = Σ_{m≤u} μ(m)/m as floats."""
    m = [0.0] * len(mu)
    acc = 0.0
    for n in range(1, len(mu)):
        acc += mu[n] / n
        m[n] = acc
    return m


def compute_S(*, Q0: int, Tmax: int, mu: list[int]) -> array:
    """
    Compute S(t) = Σ_{q≤Q0} c_q(t)/q via:
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
    """
    Compute Λ(m) for 0..n as floats:
      Λ(p^k) = log p, else 0.
    """
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


def parse_k_list(s: str) -> list[int]:
    """
    Parse comma-separated k list; supports ranges like a:b:c meaning [a,a+c,...,b].
    Examples:
      "0,1,2,10"
      "0:1000:50"  (0..1000 step 50)
    """
    out: list[int] = []
    for part in s.split(","):
        part = part.strip()
        if not part:
            continue
        if ":" in part:
            a_str, b_str, c_str = (x.strip() for x in part.split(":"))
            a, b, c = int(a_str), int(b_str), int(c_str)
            if c <= 0:
                raise ValueError("step must be positive")
            out.extend(list(range(a, b + 1, c)))
        else:
            out.append(int(part))
    # unique, sorted
    return sorted(set(out))


def compute_Fk(*, lam: array, wlin: array, N: int, k: int) -> float:
    """
    Compute F_k ≈ Σ_{n=2}^{N-2-k} Λ(n)Λ(n+k) W_lin(|2n+k-N|).
    Uses wlin indexed by |t| with 0≤|t|≤Tmax.
    """
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
    parser = argparse.ArgumentParser(description="Experiment: compute sample F_k via W_lin.")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--H", type=int, default=10_000, help="Default N=X+H unless overridden.")
    parser.add_argument("--N", type=int, default=None)
    parser.add_argument("--Tmax", type=int, default=None, help="Kernel t-range (default: 2*X).")
    parser.add_argument(
        "--k-list",
        type=str,
        default="0,2,4,10,20,50,100,200,500,1000,2000,5000,10000,20000,50000,100000",
        help="Comma-separated k values; supports ranges a:b:c.",
    )
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    N = (X + args.H) if args.N is None else args.N
    Tmax = (2 * X) if args.Tmax is None else args.Tmax
    ks = parse_k_list(args.k_list)

    if X <= 0 or Q0 <= 0 or N <= 0 or Tmax <= 0:
        raise SystemExit("Require X,Q0,N,Tmax positive.")
    if Tmax < 2 * X:
        print("warning: Tmax < 2X; some |t| indices may be truncated.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  N={N:,}  Tmax={Tmax:,}  |k|={len(ks)}")
    print(f"k list: {ks}")

    t0 = time.perf_counter()
    mu = mobius_sieve(Q0)
    t1 = time.perf_counter()
    s_arr = compute_S(Q0=Q0, Tmax=Tmax, mu=mu)
    t2 = time.perf_counter()
    # wlin[0]=0 by convention (linearization is for t≠0); leave it 0.
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

    print("\n== F_k via W_lin ==")
    print("k        F_k            |F_k|         |F_k|^2")
    sum_sq = 0.0
    max_abs = 0.0
    max_k = 0
    t5 = time.perf_counter()
    for k in ks:
        fk = compute_Fk(lam=lam, wlin=wlin, N=N, k=k)
        afk = abs(fk)
        fk2 = afk * afk
        sum_sq += fk2
        if afk > max_abs:
            max_abs = afk
            max_k = k
        print(f"{k:>6d}  {fk:>12.6e}  {afk:>12.6e}  {fk2:>12.6e}")
    t6 = time.perf_counter()
    print(f"\n[time] computed {len(ks)} F_k: {t6 - t5:.3f}s")
    print(f"sum_{'{'}k in list{'}'} |F_k|^2: {sum_sq:.6e}")
    print(f"max |F_k| in list:          {max_abs:.6e} at k={max_k}")
    print("\nNOTE: This uses W_lin, not the true W_hat, so treat magnitudes as heuristic.")


if __name__ == "__main__":
    main()

