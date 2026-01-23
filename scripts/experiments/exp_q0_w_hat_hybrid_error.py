#!/usr/bin/env python3
"""
Experiment: validate the hybrid approximation W_hat_hybrid(t) against the true W_hat(t).

True hard-arc kernel:
  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)).

Hybrid approximation used in exp_q0_fk_ttstar_w_hat_mc.py:
  W_hat_hybrid(t;Qsplit) = (1/(π t)) * Σ_{q≤Qsplit} c_q(t) * sin(2π t/(q X))
                           + (2/X) * Σ_{q>Qsplit} c_q(t)/q
where the tail Σ_{q>Qsplit} c_q(t)/q is computed from the divisor/Mertens identity.

This script samples t and reports absolute and relative errors:
  err_abs = |W_hat - W_hat_hybrid|
  err_rel = err_abs / max(|W_hat|, tiny)

This is NOT a proof and does NOT generate a Lean certificate.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
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


def compute_S_all(*, Q: int, Tmax: int, mu: list[int]) -> array:
    """
    S_Q(t) = Σ_{q≤Q} c_q(t)/q via:
      Σ_{q≤Q} c_q(t)/q = Σ_{d|t, d≤Q} M(⌊Q/d⌋),
      M(u) := Σ_{m≤u} μ(m)/m.
    """
    m = mertens_weighted(mu)
    s_arr = array("d", [0.0]) * (Tmax + 1)
    max_d = min(Q, Tmax)
    for d in range(1, max_d + 1):
        coef = m[Q // d]
        for t in range(d, Tmax + 1, d):
            s_arr[t] += coef
    return s_arr


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    """
    c_q(t) using:
      let g = gcd(q,t), h = q/g; then c_q(t) = μ(h) * φ(q)/φ(h).
    """
    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def w_hat(*, X: int, Q0: int, t: int, mu: list[int], phi: list[int]) -> float:
    s = 0.0
    for q in range(1, Q0 + 1):
        cq = ramanujan_sum(q, t, mu, phi)
        if cq:
            s += cq * math.sin(2.0 * math.pi * t / (q * X))
    return s / (math.pi * t)


def w_hat_hybrid(
    *,
    X: int,
    Q0: int,
    Qsplit: int,
    t: int,
    mu_split: list[int],
    phi_split: list[int],
    s_q0: array,
    s_qs: array,
) -> float:
    sum_small = 0.0
    two_pi_over_X = 2.0 * math.pi / X
    for q in range(1, Qsplit + 1):
        cq = ramanujan_sum(q, t, mu_split, phi_split)
        if cq:
            sum_small += cq * math.sin(two_pi_over_X * (t / q))
    exact_small = sum_small / (math.pi * t)
    tail_lin = (2.0 / X) * (s_q0[t] - s_qs[t])
    return exact_small + tail_lin


def main() -> None:
    parser = argparse.ArgumentParser(description="Experiment: hybrid W_hat approximation error.")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--Qsplit", type=int, default=500)
    parser.add_argument("--Tmax", type=int, default=None, help="Sample t in [1,Tmax]; default 2*X.")
    parser.add_argument("--samples", type=int, default=200)
    parser.add_argument("--seed", type=int, default=21)
    parser.add_argument("--parity", choices=["any", "even", "odd"], default="even")
    parser.add_argument("--include", type=str, default="", help="Comma-separated extra t values to include.")
    parser.add_argument("--top", type=int, default=8, help="Report top errors.")
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    Qsplit = args.Qsplit
    Tmax = (2 * X) if args.Tmax is None else args.Tmax
    if not (1 <= Qsplit <= Q0):
        raise SystemExit("Require 1 <= Qsplit <= Q0.")
    if X <= 0 or Q0 <= 0 or Tmax <= 0:
        raise SystemExit("Require X,Q0,Tmax positive.")
    if args.samples <= 0:
        raise SystemExit("Require --samples > 0.")

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  Qsplit={Qsplit:,}  Tmax={Tmax:,}  samples={args.samples}  parity={args.parity}  seed={args.seed}")

    t0 = time.perf_counter()
    mu_q0, phi_q0 = mobius_phi_sieve(Q0)
    mu_split, phi_split = mobius_phi_sieve(Qsplit)
    t1 = time.perf_counter()
    mu0 = mobius_sieve(Q0)
    mus = mobius_sieve(Qsplit)
    s_q0 = compute_S_all(Q=Q0, Tmax=Tmax, mu=mu0)
    s_qs = compute_S_all(Q=Qsplit, Tmax=Tmax, mu=mus)
    t2 = time.perf_counter()
    print(f"[time] sieve(mu,phi):        {t1 - t0:.3f}s")
    print(f"[time] S_Q arrays to Tmax:   {t2 - t1:.3f}s")

    rng = random.Random(args.seed)

    extra_ts: list[int] = []
    if args.include.strip():
        for part in args.include.split(","):
            part = part.strip()
            if not part:
                continue
            t = int(part)
            if t <= 0 or t > Tmax:
                raise SystemExit(f"--include t must be in [1,Tmax], got {t}")
            extra_ts.append(t)

    def sample_t() -> int:
        while True:
            t = rng.randrange(1, Tmax + 1)
            if args.parity == "even" and (t % 2 == 1):
                continue
            if args.parity == "odd" and (t % 2 == 0):
                continue
            return t

    ts = [sample_t() for _ in range(args.samples)] + extra_ts
    ts = list(dict.fromkeys(ts))
    print(f"t count: {len(ts)} (after de-dup and include)")

    tiny = 1e-30
    errs_abs: list[float] = []
    errs_rel: list[float] = []
    rows: list[tuple[int, float, float, float, float]] = []
    # (t, W_hat, W_hyb, abs_err, rel_err)
    t3 = time.perf_counter()
    for t in ts:
        wt = w_hat(X=X, Q0=Q0, t=t, mu=mu_q0, phi=phi_q0)
        wh = w_hat_hybrid(X=X, Q0=Q0, Qsplit=Qsplit, t=t, mu_split=mu_split, phi_split=phi_split, s_q0=s_q0, s_qs=s_qs)
        ae = abs(wt - wh)
        re = ae / max(abs(wt), tiny)
        errs_abs.append(ae)
        errs_rel.append(re)
        rows.append((t, wt, wh, ae, re))
    t4 = time.perf_counter()
    print(f"[time] computed errors: {t4 - t3:.3f}s")

    print("\n== Summary ==")
    print(f"max abs err:    {max(errs_abs):.6e}")
    print(f"mean abs err:   {statistics.mean(errs_abs):.6e}")
    print(f"median abs err: {statistics.median(errs_abs):.6e}")
    print(f"max rel err:    {max(errs_rel):.6g}")
    print(f"mean rel err:   {statistics.mean(errs_rel):.6g}")
    print(f"median rel err: {statistics.median(errs_rel):.6g}")

    top = min(args.top, len(rows))
    rows_by_abs = sorted(rows, key=lambda r: r[3], reverse=True)[:top]
    print(f"\nTop {top} by abs error:")
    print("rank  t        W_hat        W_hyb        abs_err      rel_err")
    for i, (t, wt, wh, ae, re) in enumerate(rows_by_abs, start=1):
        print(f"{i:>4d}  {t:>7d}  {wt:>11.4e}  {wh:>11.4e}  {ae:>11.4e}  {re:>9.3g}")


if __name__ == "__main__":
    main()

