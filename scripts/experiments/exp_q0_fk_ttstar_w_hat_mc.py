#!/usr/bin/env python3
"""
Experiment: Monte-Carlo estimate of the TT*/Parseval scale using F_k built from the (approx) true kernel W_hat.

We want data for the real hard-arc kernel, not just the linearized W_lin model.

Definitions (fixed X,Q0, integer t>0):

  W_hat(t) = (1/(π t)) * Σ_{q≤Q0} c_q(t) * sin(2π t/(q X)).

Direct evaluation of W_hat costs O(Q0) per t (Q0=30000), which is too slow to use inside F_k Monte Carlo.

So we use a hybrid approximation:
  - for q ≤ Qsplit: use the true sine term,
  - for q > Qsplit: use sin(x) ≈ x, which contributes exactly the linearized tail:
        (2/X) * Σ_{q>Qsplit} c_q(t)/q.

We precompute:
  S_Q(t) = Σ_{q≤Q} c_q(t)/q for all t ≤ Tmax via a divisor/Mertens-weighted sieve,
so that Σ_{q>Qsplit} c_q(t)/q = S_Q0(t) - S_Qsplit(t) is O(1) lookup.

Then:
  W_hat_hybrid(t) := (1/(π t)) * Σ_{q≤Qsplit} c_q(t) sin(2π t/(q X))
                     + (2/X) * (S_Q0(t) - S_Qsplit(t)).

We sample k>0, estimate:
  F_k = Σ_{n=2}^{N-2-k} Λ(n) Λ(n+k) W(|2n+k-N|)
by sampling n uniformly and rescaling.

We report:
  - F_0 estimated (optional),
  - statistics of |F_k|^2 over sampled k,
  - an extrapolated M2 estimate:
      M2_est ≈ sqrt( |F_0|^2 + 2 * max_k * mean_{k>0} |F_k|^2 ).

This is NOT a proof and does NOT generate a Lean certificate.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
import time
from array import array
from pathlib import Path


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
    c_q(t) as an integer using:
      let g = gcd(q,t), h = q/g; then c_q(t) = μ(h) * φ(q)/φ(h).
    """
    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


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


def w_hat_hybrid(
    *,
    X: int,
    Q0: int,
    Qsplit: int,
    t: int,
    mu: list[int],
    phi: list[int],
    s_q0: array,
    s_qs: array,
) -> float:
    """
    Hybrid W_hat(t) for integer t>0.
    """
    if t <= 0:
        return 0.0
    sum_small = 0.0
    two_pi_over_X = 2.0 * math.pi / X
    for q in range(1, Qsplit + 1):
        cq = ramanujan_sum(q, t, mu, phi)
        if cq:
            sum_small += cq * math.sin(two_pi_over_X * (t / q))
    exact_small = sum_small / (math.pi * t)
    tail_lin = (2.0 / X) * (s_q0[t] - s_qs[t])
    return exact_small + tail_lin


def estimate_Fk_mc(
    *,
    rng: random.Random,
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
    n_samples: int,
) -> float:
    if k < 0:
        raise ValueError("k must be nonnegative")
    n_hi = N - 2 - k
    if n_hi < 2:
        return 0.0
    n_lo = 2
    count = n_hi - n_lo + 1
    acc = 0.0
    for _ in range(n_samples):
        n = rng.randrange(n_lo, n_hi + 1)
        a = lam[n]
        if a == 0.0:
            continue
        b = lam[n + k]
        if b == 0.0:
            continue
        t = (2 * n + k) - N
        if t < 0:
            t = -t
        w = w_cache.get(t)
        if w is None:
            w = w_hat_hybrid(X=X, Q0=Q0, Qsplit=Qsplit, t=t, mu=mu, phi=phi, s_q0=s_q0, s_qs=s_qs)
            w_cache[t] = w
        acc += a * b * w
    return (count / n_samples) * acc


def quantile(values: list[float], q: float) -> float:
    """
    Empirical quantile with linear interpolation between order statistics.
    q in [0,1]. For q=0/1 returns min/max.
    """
    if not values:
        return float("nan")
    if q <= 0.0:
        return min(values)
    if q >= 1.0:
        return max(values)
    xs = sorted(values)
    n = len(xs)
    idx = q * (n - 1)
    lo = int(math.floor(idx))
    hi = int(math.ceil(idx))
    if lo == hi:
        return xs[lo]
    w = idx - lo
    return (1.0 - w) * xs[lo] + w * xs[hi]


def parse_quantiles(s: str) -> list[float]:
    out: list[float] = []
    if not s.strip():
        return out
    for part in s.split(","):
        part = part.strip()
        if not part:
            continue
        q = float(part)
        if not (0.0 <= q <= 1.0):
            raise ValueError(f"quantile must be in [0,1], got {q}")
        out.append(q)
    return out


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
    return sorted(set(out))


def read_k_file(path: str) -> list[int]:
    p = Path(path)
    if not p.exists():
        raise FileNotFoundError(path)
    ks: list[int] = []
    for line in p.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        ks.append(int(s))
    return sorted(set(ks))


def main() -> None:
    parser = argparse.ArgumentParser(description="Experiment: Monte-Carlo F_k using hybrid W_hat kernel.")
    parser.add_argument("--X", type=int, default=1_000_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--Qsplit", type=int, default=1000, help="Exact q-range for sine terms; tail linearized.")
    parser.add_argument("--H", type=int, default=10_000, help="Default N=X+H unless overridden.")
    parser.add_argument("--N", type=int, default=None)
    parser.add_argument("--Tmax", type=int, default=None, help="Precompute S_Q(t) up to Tmax (default 2*X).")
    parser.add_argument("--k-samples", type=int, default=60, help="Number of random k samples (k>0).")
    parser.add_argument("--n-samples", type=int, default=200, help="Number of n samples per k.")
    parser.add_argument("--seed", type=int, default=9)
    parser.add_argument("--include-structured", action="store_true", help="Also include k near 30k*m clusters.")
    parser.add_argument("--estimate-f0", action="store_true", help="Also MC-estimate F_0 (uses same n-samples).")
    parser.add_argument(
        "--k-list",
        type=str,
        default="",
        help="Optional explicit k values (comma-separated; supports ranges a:b:c). When set, no random k are sampled.",
    )
    parser.add_argument(
        "--k-file",
        type=str,
        default="",
        help="Optional file containing one k per line (comments with #). When set, no random k are sampled.",
    )
    parser.add_argument(
        "--quantiles",
        type=str,
        default="0.5,0.9,0.99,0.999",
        help="Comma-separated quantiles in [0,1] for |F_k|^2 (k>0 samples).",
    )
    parser.add_argument("--top", type=int, default=10, help="Report top-k samples by |F_k|.")
    args = parser.parse_args()

    X = args.X
    Q0 = args.Q0
    Qsplit = args.Qsplit
    N = (X + args.H) if args.N is None else args.N
    Tmax = (2 * X) if args.Tmax is None else args.Tmax
    if not (1 <= Qsplit <= Q0):
        raise SystemExit("Require 1 <= Qsplit <= Q0.")
    if Tmax < 1:
        raise SystemExit("Require Tmax >= 1.")
    if args.k_samples <= 0 or args.n_samples <= 0:
        raise SystemExit("Require positive sample sizes.")
    if Tmax < 2 * X:
        print("warning: Tmax < 2*X; t values might exceed precomputed range if N differs from X.")

    print("== Parameters ==")
    print(
        f"X={X:,}  Q0={Q0:,}  Qsplit={Qsplit:,}  N={N:,}  Tmax={Tmax:,}  "
        f"k_samples={args.k_samples}  n_samples={args.n_samples}  seed={args.seed}"
    )
    print(f"include_structured={args.include_structured}  estimate_f0={args.estimate_f0}")

    t0 = time.perf_counter()
    mu_phi, phi = mobius_phi_sieve(Qsplit)  # need mu,phi up to Qsplit for exact small-q part
    # extend mu,phi to Q0 for ramanujan_sum(q,t) with q<=Qsplit only: mu,phi indices need <=Qsplit.
    # For the linearized tail (q>Qsplit) we use precomputed S_Q arrays, no ramanujan_sum calls.
    t1 = time.perf_counter()
    mu_q0 = mobius_sieve(Q0)
    mu_qs = mobius_sieve(Qsplit)
    t2 = time.perf_counter()
    s_q0 = compute_S_all(Q=Q0, Tmax=Tmax, mu=mu_q0)
    t3 = time.perf_counter()
    s_qs = compute_S_all(Q=Qsplit, Tmax=Tmax, mu=mu_qs)
    t4 = time.perf_counter()
    lam = von_mangoldt_array(N)
    t5 = time.perf_counter()
    print(f"[time] sieve(mu,phi) to Qsplit: {t1 - t0:.3f}s")
    print(f"[time] sieve(mu) Q0/Qsplit:     {t2 - t1:.3f}s")
    print(f"[time] S_Q0(t) to Tmax:         {t3 - t2:.3f}s")
    print(f"[time] S_Qsplit(t) to Tmax:     {t4 - t3:.3f}s")
    print(f"[time] Λ array to N:            {t5 - t4:.3f}s")

    rng = random.Random(args.seed)

    max_k = N - 4
    ks: list[int]
    if args.k_file.strip():
        ks = read_k_file(args.k_file)
    elif args.k_list.strip():
        ks = parse_k_list(args.k_list)
    else:
        ks = [rng.randrange(1, max_k + 1) for _ in range(args.k_samples)]
        if args.include_structured:
            for base in [30_000, 60_000, 90_000, 120_000, 150_000, 180_000]:
                for off in [0, 200, 400, 600, 800, 1000]:
                    k = base + off
                    if 1 <= k <= max_k:
                        ks.append(k)
        ks = list(dict.fromkeys(ks))

    # Filter k into the valid range [1,max_k] (and keep 0 only for f0 if requested separately)
    ks = [k for k in ks if 1 <= k <= max_k]
    if not ks:
        raise SystemExit("No valid k values to test (after filtering to 1..N-4).")

    w_cache: dict[int, float] = {}

    f0 = 0.0
    if args.estimate_f0:
        t6 = time.perf_counter()
        f0 = estimate_Fk_mc(
            rng=rng,
            lam=lam,
            w_cache=w_cache,
            X=X,
            Q0=Q0,
            Qsplit=Qsplit,
            mu=mu_phi,
            phi=phi,
            s_q0=s_q0,
            s_qs=s_qs,
            N=N,
            k=0,
            n_samples=args.n_samples,
        )
        t7 = time.perf_counter()
        print(f"\nF_0 (MC): {f0:.6e}  |F_0|^2: {abs(f0)**2:.6e}  [time {t7 - t6:.3f}s]")

    abs_sq: list[float] = []
    max_abs = 0.0
    max_k_seen = 0
    t8 = time.perf_counter()
    for k in ks:
        fk = estimate_Fk_mc(
            rng=rng,
            lam=lam,
            w_cache=w_cache,
            X=X,
            Q0=Q0,
            Qsplit=Qsplit,
            mu=mu_phi,
            phi=phi,
            s_q0=s_q0,
            s_qs=s_qs,
            N=N,
            k=k,
            n_samples=args.n_samples,
        )
        afk = abs(fk)
        abs_sq.append(afk * afk)
        if afk > max_abs:
            max_abs = afk
            max_k_seen = k
    t9 = time.perf_counter()

    print(f"\n[time] computed {len(ks)} F_k estimates: {t9 - t8:.3f}s")
    print(f"kernel cache size: {len(w_cache):,} distinct t values")

    mean_sq = statistics.mean(abs_sq) if abs_sq else 0.0
    med_sq = statistics.median(abs_sq) if abs_sq else 0.0
    max_sq = max(abs_sq) if abs_sq else 0.0
    print("\n== Sample stats over k>0 ==")
    print(f"mean |F_k|^2:   {mean_sq:.6e}")
    print(f"median |F_k|^2: {med_sq:.6e}")
    print(f"max |F_k|:      {max_abs:.6e} at k={max_k_seen}")

    qs = parse_quantiles(args.quantiles)
    if qs:
        print("\nQuantiles of |F_k|^2 over sampled k>0:")
        for q in qs:
            print(f"  q={q:>7g}: {quantile(abs_sq, q):.6e}")

    # Report top |F_k| entries (approx, uses the same sampled set)
    if args.top > 0:
        # Recompute F_k for top tracking, but only store (|F_k|, k)
        # We already computed afk for each k but did not store it; recompute cheaply using the cache.
        # This keeps code simple and still fast (w_cache has most t values already).
        top_n = min(args.top, len(ks))
        if top_n > 0:
            items: list[tuple[float, int]] = []
            for k in ks:
                fk = estimate_Fk_mc(
                    rng=rng,
                    lam=lam,
                    w_cache=w_cache,
                    X=X,
                    Q0=Q0,
                    Qsplit=Qsplit,
                    mu=mu_phi,
                    phi=phi,
                    s_q0=s_q0,
                    s_qs=s_qs,
                    N=N,
                    k=k,
                    n_samples=args.n_samples,
                )
                items.append((abs(fk), k))
            items.sort(reverse=True)
            print(f"\nTop {top_n} sampled k by |F_k| (MC):")
            for i, (afk, k) in enumerate(items[:top_n], start=1):
                print(f"{i:>4d}  k={k:>7d}  |F_k|≈{afk:.6e}  |F_k|^2≈{afk*afk:.6e}")

    # Extrapolate M2 scale from sampled |F_k|^2 over k>0:
    m2_sq_est = (abs(f0) ** 2) + 2.0 * max_k * mean_sq
    m2_est = math.sqrt(max(0.0, m2_sq_est))
    print("\n== Extrapolated TT* scale (heuristic) ==")
    print(f"max_k (support for k>0): {max_k:,}")
    print(f"M2_est ≈ sqrt(|F0|^2 + 2*max_k*E|F_k|^2): {m2_est:,.1f}")


if __name__ == "__main__":
    main()
