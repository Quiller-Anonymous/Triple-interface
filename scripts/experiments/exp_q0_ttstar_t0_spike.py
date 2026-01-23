#!/usr/bin/env python3
"""
Experiment (Step5): t=0 ("constant mode") spike in the TT*/Toeplitz coefficients F_k.

In the Toeplitz expansion, for fixed (X,N) and k>0, the term with
  t = |2n + k - N| = 0
occurs only when N-k is even and n = (N-k)/2.
Then n+k = (N+k)/2 and the contribution from the t=0 kernel mode is:

  F_k[t=0] = Λ(n) Λ(n+k) * W(0),

where W(0) is the α-weight constant mode (mean) for the major-arc weight.

This script:
  - computes W_hard(0) exactly from φ(q)/q (disjoint hard arcs),
  - computes W_smooth(0) exactly from the wTextbook L1 mass (3/(qX) per arc),
  - scans n to find the largest Λ(n)Λ(N-n) (equivalently, largest |F_k[t=0]|),
  - evaluates t=0 contributions on chosen k sets (random, k-file, structured clusters).

This is NOT a proof and does NOT generate a Lean certificate.
"""

from __future__ import annotations

import argparse
import math
import random
import time
from array import array
from pathlib import Path


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


def w0_hard(*, X: int, Q0: int, phi: list[int]) -> float:
    # disjoint hard arcs: sum_{q<=Q0} φ(q) * 2/(qX)
    acc = 0.0
    for q in range(1, Q0 + 1):
        acc += phi[q] / q
    return (2.0 / X) * acc


def w0_smooth(*, X: int, Q0: int, phi: list[int]) -> float:
    # wTextbook mass per arc is exactly 3/(qX)
    acc = 0.0
    for q in range(1, Q0 + 1):
        acc += phi[q] / q
    return (3.0 / X) * acc


def parse_int_list(path: Path) -> list[int]:
    out: list[int] = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        out.append(int(line))
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description="Experiment: t=0 spike in F_k.")
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--Q0", type=int, default=30_000)
    ap.add_argument("--H", type=int, default=10_000, help="Default N=X+H unless overridden.")
    ap.add_argument("--N", type=int, default=None)
    ap.add_argument("--seed", type=int, default=50)
    ap.add_argument("--k-samples", type=int, default=2000, help="Random k values to sample.")
    ap.add_argument("--k-file", type=str, default=None)
    ap.add_argument("--include-structured", action="store_true", help="Add k near 30k*m clusters.")
    ap.add_argument("--top", type=int, default=30, help="Report top n terms in the n-scan.")
    args = ap.parse_args()

    X = args.X
    Q0 = args.Q0
    H = args.H
    N = args.N if args.N is not None else X + H
    rng = random.Random(args.seed)

    print("== Parameters ==")
    print(f"X={X:,}  Q0={Q0:,}  N={N:,}  seed={args.seed}  k_samples={args.k_samples:,}")

    t0 = time.time()
    _, phi = mobius_phi_sieve(Q0)
    print(f"[time] phi sieve to Q0: {time.time()-t0:.3f}s")

    w0h = w0_hard(X=X, Q0=Q0, phi=phi)
    w0s = w0_smooth(X=X, Q0=Q0, phi=phi)
    print(f"W0 hard  (meas hard arcs):   {w0h:.9e}")
    print(f"W0 smooth(wTextbook mass):  {w0s:.9e}  (=1.5 * hard)")

    t1 = time.time()
    lam = von_mangoldt_array(N)
    print(f"[time] Λ array to N: {time.time()-t1:.3f}s")

    # Scan n to find max of Λ(n)Λ(N-n), i.e. maximal t=0 spike magnitude.
    # (This corresponds to k = N - 2n, so k>0 means n < N/2.)
    top = args.top
    best: list[tuple[float, int]] = []  # (prod, n)

    for n in range(2, N - 1):
        a = lam[n]
        if a == 0.0:
            continue
        b = lam[N - n]
        if b == 0.0:
            continue
        prod = a * b
        if len(best) < top:
            best.append((prod, n))
            best.sort()
        elif prod > best[0][0]:
            best[0] = (prod, n)
            best.sort()

    best.sort(reverse=True)
    print(f"\n== Top {len(best)} t=0 spike candidates (by Λ(n)Λ(N-n)) ==")
    for i, (prod, n) in enumerate(best, start=1):
        k = N - 2 * n
        if k <= 0:
            continue
        print(
            f"{i:3d}  n={n:7d}  k={k:7d}  "
            f"Λ(n)Λ(N-n)≈{prod:9.6f}  "
            f"|F_k[t=0]|_hard≈{w0h*prod:9.6f}  |F_k[t=0]|_smooth≈{w0s*prod:9.6f}"
        )

    # Evaluate t=0 contributions on a k sample set.
    k_set: set[int] = set()
    if args.k_file:
        k_set.update(parse_int_list(Path(args.k_file)))
    for _ in range(args.k_samples):
        k_set.add(rng.randrange(1, max(2, N - 3)))
    if args.include_structured:
        for m in range(1, 34):
            base = 30_000 * m
            for off in range(-1000, 1001, 200):
                k_set.add(base + off)

    # Filter admissible k and compute contributions.
    k_list = sorted(k for k in k_set if 1 <= k <= (N - 4))
    hard_vals: list[float] = []
    smooth_vals: list[float] = []
    for k in k_list:
        if (N - k) & 1:
            continue
        n = (N - k) // 2
        if not (2 <= n <= N - 2 - k):
            continue
        a = lam[n]
        b = lam[n + k]
        if a == 0.0 or b == 0.0:
            continue
        prod = a * b
        hard_vals.append(w0h * prod)
        smooth_vals.append(w0s * prod)

    hard_vals.sort()
    smooth_vals.sort()

    def qtile(xs: list[float], q: float) -> float:
        if not xs:
            return float("nan")
        if q <= 0:
            return xs[0]
        if q >= 1:
            return xs[-1]
        idx = q * (len(xs) - 1)
        lo = int(math.floor(idx))
        hi = int(math.ceil(idx))
        if lo == hi:
            return xs[lo]
        w = idx - lo
        return (1.0 - w) * xs[lo] + w * xs[hi]

    print(f"\n== t=0 contribution stats over sampled k (count={len(hard_vals)}) ==")
    for name, xs in [("hard", hard_vals), ("smooth", smooth_vals)]:
        if not xs:
            print(f"{name}: no nonzero t=0 contributions found")
            continue
        print(f"{name}: max={xs[-1]:.6e}  q99={qtile(xs,0.99):.6e}  q90={qtile(xs,0.9):.6e}  median={qtile(xs,0.5):.6e}")


if __name__ == "__main__":
    main()

