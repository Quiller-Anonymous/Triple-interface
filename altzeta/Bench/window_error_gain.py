#!/usr/bin/env python3
"""
AltZeta/Bench/window_error_gain.py

Small benchmark helper for the B2 workflow:

Given pointwise error envelopes E_AZ(x) and E_zeta(x) on a grid in [X,2X],
compute the gain ratio

    gain(x) = E_zeta(x) / E_AZ(x)

and report basic statistics (min/median, how many points have gain > 1, etc).

Input format (CSV):
  x,e_az,e_zeta

Usage:
  python3 AltZeta/Bench/window_error_gain.py --csv data.csv
  python3 AltZeta/Bench/window_error_gain.py --demo --X 1e6 --points 200
"""

from __future__ import annotations

import argparse
import csv
import math
import statistics
from dataclasses import dataclass
from typing import Iterable, List, Optional, Tuple


@dataclass(frozen=True)
class Row:
    x: float
    e_az: float
    e_zeta: float

    def gain(self) -> Optional[float]:
        if self.e_az <= 0.0:
            return None
        return self.e_zeta / self.e_az


def read_csv(path: str) -> List[Row]:
    rows: List[Row] = []
    with open(path, "r", newline="") as f:
        reader = csv.DictReader(f)
        for i, r in enumerate(reader, start=2):
            try:
                x = float(r["x"])
                e_az = float(r["e_az"])
                e_zeta = float(r["e_zeta"])
            except Exception as exc:
                raise ValueError(f"{path}:{i}: bad row {r}") from exc
            rows.append(Row(x=x, e_az=e_az, e_zeta=e_zeta))
    return rows


def demo_rows(X: float, points: int) -> List[Row]:
    # Toy model: E_AZ(x) = x^0.4, E_zeta(x) = 1.5 * x^0.4.
    rows: List[Row] = []
    for k in range(points):
        t = (k + 0.5) / points
        x = X * (1.0 + t)  # x in (X, 2X)
        e_az = x ** 0.4
        e_zeta = 1.5 * e_az
        rows.append(Row(x=x, e_az=e_az, e_zeta=e_zeta))
    return rows


def summarize(rows: Iterable[Row]) -> Tuple[int, int, int, List[float]]:
    total = 0
    good = 0
    better = 0
    gains: List[float] = []
    for r in rows:
        total += 1
        g = r.gain()
        if g is None or math.isnan(g) or math.isinf(g):
            continue
        good += 1
        gains.append(g)
        if g > 1.0:
            better += 1
    return total, good, better, gains


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--csv", help="Input CSV with columns x,e_az,e_zeta")
    ap.add_argument("--demo", action="store_true", help="Use a built-in toy model")
    ap.add_argument("--X", type=float, default=1e6, help="Demo window start X")
    ap.add_argument("--points", type=int, default=200, help="Number of grid points (demo)")
    args = ap.parse_args()

    if bool(args.csv) == bool(args.demo):
        ap.error("Choose exactly one of --csv or --demo")

    rows = read_csv(args.csv) if args.csv else demo_rows(args.X, args.points)

    total, good, better, gains = summarize(rows)
    if not gains:
        print(f"rows={total} usable=0 (all had e_az<=0 or invalid ratios)")
        return 2

    gains_sorted = sorted(gains)
    print(f"rows={total} usable={good} gain>1={better}")
    print(f"gain_min={gains_sorted[0]:.6g}")
    print(f"gain_median={statistics.median(gains_sorted):.6g}")
    print(f"gain_mean={statistics.mean(gains_sorted):.6g}")
    print(f"gain_max={gains_sorted[-1]:.6g}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

