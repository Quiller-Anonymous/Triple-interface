#!/usr/bin/env python3
"""
AltZeta/Bench/b2_real_envelopes.py

Generate a CSV grid of the *envelope functions* for the canonical B2 parameter pack.

This does NOT compute Ψ_K itself; it only computes the current envelope

  E_AZ(x) = CGamma + sqrt(x) * S_cert

as defined in `AltZeta/B2RealTrunc.lean` (with values sourced from `Goldbach/Census/Data.lean`).

The intent is to feed the output into `AltZeta/Bench/window_error_gain.py`.

Example:
  python3 AltZeta/Bench/b2_real_envelopes.py --X 1e6 --points 200 --zeta-mult 2 > out.csv
  python3 AltZeta/Bench/window_error_gain.py --csv out.csv
"""

from __future__ import annotations

import argparse
import math
import sys


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--X", type=float, required=True, help="Window start X (use x in [X,2X])")
    ap.add_argument("--points", type=int, default=200, help="Number of grid points")
    ap.add_argument("--cgamma", type=float, default=0.25, help="CGamma constant (default 1/4)")
    ap.add_argument("--s-cert", type=float, default=0.1, help="S_cert constant (default 1/10)")
    ap.add_argument("--zeta-mult", type=float, default=2.0, help="Baseline multiplier: E_zeta = m * E_AZ")
    args = ap.parse_args()

    X = args.X
    if not (X > 0):
        ap.error("--X must be > 0")
    if args.points <= 0:
        ap.error("--points must be positive")

    cgamma = args.cgamma
    s_cert = args.s_cert
    m = args.zeta_mult

    out = sys.stdout
    out.write("x,e_az,e_zeta\n")
    for k in range(args.points):
        t = (k + 0.5) / args.points
        x = X * (1.0 + t)  # x in (X,2X)
        e_az = cgamma + math.sqrt(x) * s_cert
        e_zeta = m * e_az
        out.write(f"{x:.17g},{e_az:.17g},{e_zeta:.17g}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

