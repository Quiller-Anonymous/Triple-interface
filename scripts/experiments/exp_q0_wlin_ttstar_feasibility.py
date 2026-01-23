#!/usr/bin/env python3
"""
Experiment: Q0-route TT*/Toeplitz feasibility via W_lin(t).

This is NOT a proof and it does NOT generate a Lean certificate. It is a repeatable,
parameterized sanity check intended to guide "successive approximation" of constants.

We study the hard major-arc Fourier kernel

  Ŵ_X(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X))      (t ≠ 0),

and its linearized model (sin y ≈ y):

  W_lin(t) := (2/X) * Σ_{q≤Q0} c_q(t)/q.

The key Ramanujan identity used for fast evaluation of Σ_{q≤Q0} c_q(t)/q is:

  Σ_{q≤Q0} c_q(t)/q = Σ_{d|t, d≤Q0} M(⌊Q0/d⌋),
  M(u) := Σ_{m≤u} μ(m)/m.

Default settings mimic the Step-5 "first experiment" (X=1e6, Q0=30000, t≤2e6).
"""

from __future__ import annotations

import argparse
import math
import random
import time
from array import array


def mobius_phi_sieve(n: int) -> tuple[list[int], list[int]]:
    """Return (mu, phi) for 0..n via a linear sieve."""
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
    """M(u) = Σ_{m≤u} μ(m)/m as floats, for u=0..len(mu)-1."""
    m = [0.0] * len(mu)
    acc = 0.0
    for n in range(1, len(mu)):
        acc += mu[n] / n
        m[n] = acc
    return m


def primes_up_to(n: int) -> list[int]:
    if n < 2:
        return []
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    limit = int(math.isqrt(n))
    for p in range(2, limit + 1):
        if sieve[p]:
            start = p * p
            step = p
            sieve[start : n + 1 : step] = b"\x00" * (((n - start) // step) + 1)
    return [i for i in range(2, n + 1) if sieve[i]]


def von_mangoldt_sq_sum(n: int) -> float:
    """Σ_{m≤n} Λ(m)^2 = Σ_{p^k≤n} (log p)^2 as a float."""
    total = 0.0
    for p in primes_up_to(n):
        lp2 = math.log(p) ** 2
        pk = p
        while pk <= n:
            total += lp2
            pk *= p
    return total


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    """
    c_q(t) as an integer using:
      c_q(t) = Σ_{d|gcd(q,t)} d μ(q/d)
    but computed via the standard closed form:
      let g = gcd(q,t), h = q/g; then c_q(t) = μ(h) * φ(q)/φ(h).
    """
    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def sample_w_hat(
    *,
    X: int,
    Q0: int,
    samples: int,
    tmax: int,
    seed: int,
    mu: list[int],
    phi: list[int],
    parity: str,
) -> dict[str, float]:
    rng = random.Random(seed)
    max_abs = 0.0
    mean_abs = 0.0
    mean_sq = 0.0
    for i in range(1, samples + 1):
        if parity == "all":
            t = rng.randint(1, tmax)
        elif parity == "even":
            t = 2 * rng.randint(1, tmax // 2)
        elif parity == "odd":
            t = 2 * rng.randint(0, (tmax - 1) // 2) + 1
        else:
            raise ValueError(f"unexpected parity: {parity!r}")
        s = 0.0
        for q in range(1, Q0 + 1):
            cq = ramanujan_sum(q, t, mu, phi)
            if cq:
                s += cq * math.sin(2.0 * math.pi * t / (q * X))
        w = s / (math.pi * t)
        aw = abs(w)
        max_abs = max(max_abs, aw)
        mean_abs += aw
        mean_sq += w * w
        if i % 50 == 0:
            pass
    mean_abs /= samples
    mean_sq /= samples
    return {"max_abs": max_abs, "mean_abs": mean_abs, "mean_sq": mean_sq}


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Experiment: linearized hard-arc Toeplitz kernel W_lin(t) and TT* feasibility.",
    )
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument(
        "--Tmax",
        type=int,
        default=None,
        help="Max t to scan (default: 2*X).",
    )
    parser.add_argument(
        "--H",
        type=int,
        default=10_000,
        help="Window size H (used only to set default N=X+H for Λ² sum).",
    )
    parser.add_argument(
        "--N",
        type=int,
        default=None,
        help="Upper limit for Σ_{n≤N} Λ(n)^2 (default: X+H).",
    )
    parser.add_argument(
        "--sample-w-hat",
        action="store_true",
        help="Also sample true hard-arc |W_hat(t)| for random t (slow: O(Q0*samples)).",
    )
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--tmax-sample", type=int, default=2_000_000)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--sample-parity",
        choices=["all", "even", "odd"],
        default="all",
        help="Restrict sampled t to a parity class (default: all).",
    )
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    Tmax = 2 * X if args.Tmax is None else args.Tmax
    N = X + args.H if args.N is None else args.N

    if X <= 0 or Q0 <= 0 or Tmax <= 0 or N <= 0:
        raise SystemExit("Require X,Q0,Tmax,N positive.")
    if Tmax < 1:
        raise SystemExit("Require Tmax ≥ 1.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  Tmax={Tmax:,}  N={N:,}")

    t0 = time.perf_counter()
    mu, phi = mobius_phi_sieve(Q0)
    m = mertens_weighted(mu)
    t1 = time.perf_counter()
    print(f"[time] sieve(mu,phi) + M(u): {t1 - t0:.3f}s")

    max_d = min(Q0, Tmax)
    s_arr = array("d", [0.0]) * (Tmax + 1)
    s_local = s_arr
    m_local = m
    q0_local = Q0
    for d in range(1, max_d + 1):
        coef = m_local[q0_local // d]
        for t in range(d, Tmax + 1, d):
            s_local[t] += coef
    t2 = time.perf_counter()
    print(f"[time] divisor-sieve S(t) for t≤{Tmax:,}: {t2 - t1:.3f}s")

    sumsq = 0.0
    sumsq_par = [0.0, 0.0]
    cnt_par = [0, 0]
    maxabs = 0.0
    t_max = 1
    maxabs_par = [0.0, 0.0]
    t_max_par = [1, 1]
    for t in range(1, Tmax + 1):
        v = s_local[t]
        vv = v * v
        sumsq += vv
        p = t & 1
        sumsq_par[p] += vv
        cnt_par[p] += 1
        av = abs(v)
        if av > maxabs:
            maxabs = av
            t_max = t
        if av > maxabs_par[p]:
            maxabs_par[p] = av
            t_max_par[p] = t
    t3 = time.perf_counter()
    print(f"[time] stats over t≤{Tmax:,}: {t3 - t2:.3f}s")

    mean_s2 = sumsq / Tmax
    mean_s2_par = [sumsq_par[p] / cnt_par[p] for p in (0, 1)]
    mean_wlin2 = (4.0 / (X * X)) * mean_s2
    mean_wlin2_par = [(4.0 / (X * X)) * mean_s2_par[p] for p in (0, 1)]
    bw_est_par = [N * mean_wlin2_par[p] for p in (0, 1)]
    bw_est = max(bw_est_par)
    bw_est_all = N * mean_wlin2
    bw_est_avg_parity = 0.5 * (bw_est_par[0] + bw_est_par[1])

    print("\n== Linearized kernel statistics ==")
    print(f"mean(S(t)^2) over 1..Tmax: {mean_s2:.6g}")
    print(f"mean(S(t)^2) even t:       {mean_s2_par[0]:.6g}")
    print(f"mean(S(t)^2) odd  t:       {mean_s2_par[1]:.6g}")
    print(f"max |S(t)|:                {maxabs:.6g} at t={t_max}")
    print(f"max |S(t)| even:           {maxabs_par[0]:.6g} at t={t_max_par[0]}")
    print(f"max |S(t)| odd:            {maxabs_par[1]:.6g} at t={t_max_par[1]}")
    print(f"mean(W_lin(t)^2):          {mean_wlin2:.6g}")
    print(f"mean(W_lin(t)^2) even:     {mean_wlin2_par[0]:.6g}")
    print(f"mean(W_lin(t)^2) odd:      {mean_wlin2_par[1]:.6g}")
    print(f"BW_est (even k):           {bw_est_par[0]:.6g}")
    print(f"BW_est (odd  k):           {bw_est_par[1]:.6g}")
    print(f"BW_est (max parity):       {bw_est:.6g}")
    print(f"BW_est (all t mean):       {bw_est_all:.6g}")
    print(f"BW_est (avg even/odd):     {bw_est_avg_parity:.6g}")

    t4 = time.perf_counter()
    lam2 = von_mangoldt_sq_sum(N)
    t5 = time.perf_counter()
    print(f"\n[time] Σ Λ(n)^2 up to N={N:,}: {t5 - t4:.3f}s")
    print(f"Σ_{'{'}n≤N{'}'} Λ(n)^2:            {lam2:.6f}")

    m2_est = math.sqrt(bw_est) * lam2
    m2_est_all = math.sqrt(bw_est_all) * lam2
    m2_est_avg_parity = math.sqrt(bw_est_avg_parity) * lam2
    m2_required_bw = (50_000.0 / lam2) ** 2
    print("\n== TT* feasibility (heuristic) ==")
    print("This uses the crude model: BW ≈ N * mean(W_lin(t)^2) and M2 ≈ sqrt(BW) * ΣΛ^2.")
    print(f"M2_est (max parity) ≈       {m2_est:.3f}")
    print(f"M2_est (all t mean) ≈       {m2_est_all:.3f}")
    print(f"M2_est (avg even/odd) ≈     {m2_est_avg_parity:.3f}")
    print(f"BW needed for M2=50,000:     {m2_required_bw:.6g}")
    print(f"BW_est(max parity)/needed:   {bw_est / m2_required_bw:.3f}")
    print(f"BW_est(all mean)/needed:     {bw_est_all / m2_required_bw:.3f}")
    print(f"BW_est(avg even/odd)/needed: {bw_est_avg_parity / m2_required_bw:.3f}")

    if args.sample_w_hat:
        t6 = time.perf_counter()
        stats = sample_w_hat(
            X=X,
            Q0=Q0,
            samples=args.samples,
            tmax=args.tmax_sample,
            seed=args.seed,
            mu=mu,
            phi=phi,
            parity=args.sample_parity,
        )
        t7 = time.perf_counter()
        print(
            f"\n[time] sampled W_hat(t) ({args.samples} samples, {args.sample_parity} t, t≤{args.tmax_sample:,}): {t7 - t6:.3f}s"
        )
        print("== Sampled true hard-arc kernel W_hat ==")
        print(f"parity:                      {args.sample_parity}")
        print(f"mean |W_hat|:                {stats['mean_abs']:.6g}")
        print(f"mean  W_hat^2:               {stats['mean_sq']:.6g}")
        print(f"max  |W_hat|:                {stats['max_abs']:.6g}")


if __name__ == "__main__":
    main()
