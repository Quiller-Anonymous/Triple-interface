#!/usr/bin/env python3
"""
Raw support-convention audit for the zero-mode scalar.

This script compares ordered and unordered pair conventions for both:

- the exact zero-mode numerator, and
- the geometric zero baseline.

The purpose is to test whether the remaining scalar comes from a mismatch between ordered and
unordered `(n,m)` support conventions before any downstream normalization.
"""

from __future__ import annotations

import argparse
import math
from typing import Dict

from exp_q0_minor_singularity_exact_harness import H, k_full_on_sbg, prime_window_payload, sum_by_s
from exp_q0_minor_zero_mode_refinement import even_window, singular_series_shape, smallest_prime_factors, sum_by_s_uniform_fast


def parse_x_list(spec: str) -> list[int]:
    out: list[int] = []
    for piece in spec.split(","):
        piece = piece.strip()
        if piece:
            out.append(int(piece))
    if not out:
        raise SystemExit("empty --X-list")
    return out


def route_window_floor(X: int) -> float:
    return (1.0 / 800.0) * (1.0 / (math.log(X + H) ** 2))


def mean(xs: list[float]) -> float:
    return sum(xs) / len(xs)


def variance(xs: list[float]) -> float:
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs) / len(xs)


def summarize(label: str, vals: list[float]) -> None:
    m = mean(vals)
    std = math.sqrt(variance(vals))
    cv = 0.0 if abs(m) <= 1e-30 else std / abs(m)
    print(f"{label:34s} mean={m:.12e}  std={std:.12e}  cv={cv:.12e}")


def prime_diag_map(X: int) -> Dict[int, float]:
    payload = dict(prime_window_payload(X))
    k0 = k_full_on_sbg(0)
    out: Dict[int, float] = {}
    for n, a in payload.items():
        out[2 * n] = (a * a) * k0
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Zero-mode raw support convention diagnostic.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    spf = smallest_prime_factors(max(Xs) + H)
    k0 = k_full_on_sbg(0)

    for X in Xs:
        Ns = even_window(X, args.step)
        cX = route_window_floor(X)
        sigma = {N: singular_series_shape(N, spf) for N in Ns}

        exact_ordered = sum_by_s(X)
        exact_diag = prime_diag_map(X)
        geom_ordered = sum_by_s_uniform_fast(X)

        r_oo: list[float] = []
        r_ou: list[float] = []
        r_uo: list[float] = []
        r_uu: list[float] = []

        for N in Ns:
            sig = sigma[N]
            if abs(sig) <= 1e-30 or abs(cX) <= 1e-30:
                continue

            eo = exact_ordered.get(N, 0.0)
            ed = exact_diag.get(N, 0.0)
            eu = 0.5 * (eo + ed)

            go = geom_ordered.get(N, 0.0)
            gd = k0
            gu = 0.5 * (go + gd)

            if abs(go) > 1e-30:
                r_oo.append(eo / (go * sig * cX))
                r_uo.append(eu / (go * sig * cX))
            if abs(gu) > 1e-30:
                r_ou.append(eo / (gu * sig * cX))
                r_uu.append(eu / (gu * sig * cX))

        print(f"== X={X:,} ==")
        print(f"k0={k0:.12e}  c_X={cX:.12e}")
        print()
        summarize("exact ordered / geom ordered", r_oo)
        summarize("exact ordered / geom unordered", r_ou)
        summarize("exact unordered / geom ordered", r_uo)
        summarize("exact unordered / geom unordered", r_uu)
        print()


if __name__ == "__main__":
    main()
