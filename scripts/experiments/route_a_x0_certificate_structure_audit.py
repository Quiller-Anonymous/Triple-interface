#!/usr/bin/env python3
"""Audit structural information in the saved X0 certificate payloads.

This script does not rebuild any Lean certificate. It reads the exact rational
payloads produced by the historical X0 build and checks the mode structure that
is otherwise obscured by the generated-file decomposition.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_PERIODIC = (
    ROOT
    / ".cache/periodic_main_exact_records_full"
    / "periodic_main_ordered_nonzero_records.json"
)
DEFAULT_ZERO = ROOT / ".cache/periodic_main_ordered_zero_records.json"
DEFAULT_LCM = (
    ROOT
    / ".cache/periodic_main_exact_records_full"
    / "periodic_main_ordered_nonzero_without_row_five_nondyadic_lcm_payload.json"
)
DEFAULT_BOUNDARY = ROOT / ".cache/boundary_active_exact_combine_report.txt"
DEFAULT_LEAN = (
    ROOT
    / "Goldbach/Cert/MajorArcModules/Q0MinorZeroModeNormalizedAverage.lean"
)


# Exact outputs of --emit-boundary-pair-rat at X0. These are checked below
# against the diagonal and periodic-main payloads, rather than used as inputs
# to either computation.
LOW_MODE_BOUNDARY_PER_ORIENTATION = {
    3: Fraction(75, 8),
    5: Fraction(39_062_500, 25_010_001),
    7: Fraction(17_347_225, 300_120_012),
}

LOW_MODE_DIAGONAL_DEFS = {
    3: "surrogateDiagMainTerm3X0RatCert",
    5: "surrogateDiagMainTerm5X0RatCert",
    7: "surrogateDiagMainTerm7X0RatCert",
}


def load_json(path: Path) -> dict:
    if not path.is_file():
        raise SystemExit(f"missing required payload: {path}")
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def record_value(record: dict) -> Fraction:
    return Fraction(int(record["value_num"]), int(record["value_den"]))


def dyadic_base(q: int, q2: int) -> int | None:
    if q % 2 == 1 and q2 == 2 * q:
        return q
    if q2 % 2 == 1 and q == 2 * q2:
        return q2
    return None


def decimal(value: Fraction, digits: int = 18) -> str:
    getcontext().prec = max(digits + 10, 40)
    out = Decimal(value.numerator) / Decimal(value.denominator)
    return f"{out:.{digits}f}"


def percent(numerator: Fraction, denominator: Fraction) -> str:
    if denominator == 0:
        return "0.000000000"
    return decimal(100 * numerator / denominator, 9)


def parse_boundary_fraction(text: str, label: str) -> Fraction:
    pattern = re.compile(
        rf"{re.escape(label)}\s*=\s*\((-?\d+)\s*:\s*Q\)\s*/\s*(\d+)".replace(
            "Q", "\u211a"
        )
    )
    match = pattern.search(text)
    if match is None:
        raise SystemExit(f"could not parse {label} from boundary report")
    return Fraction(int(match.group(1)), int(match.group(2)))


def parse_lean_rat_def(text: str, name: str) -> Fraction:
    pattern = re.compile(
        rf"def\s+{re.escape(name)}\s*:\s*\u211a\s*:=\s*"
        rf"\((\d+)\s*:\s*\u211a\)\s*/\s*(\d+)"
    )
    match = pattern.search(text)
    if match is None:
        raise SystemExit(f"could not parse Lean rational definition {name}")
    return Fraction(int(match.group(1)), int(match.group(2)))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--periodic", type=Path, default=DEFAULT_PERIODIC)
    parser.add_argument("--zero", type=Path, default=DEFAULT_ZERO)
    parser.add_argument("--lcm", type=Path, default=DEFAULT_LCM)
    parser.add_argument("--boundary", type=Path, default=DEFAULT_BOUNDARY)
    parser.add_argument("--lean-source", type=Path, default=DEFAULT_LEAN)
    args = parser.parse_args()

    periodic = load_json(args.periodic)
    zero = load_json(args.zero)
    lcm_payload = load_json(args.lcm)
    boundary_text = args.boundary.read_text(encoding="utf-8")
    lean_text = args.lean_source.read_text(encoding="utf-8")

    records = periodic["records"]
    if len(records) != int(periodic["ordered_nonzero_records"]):
        raise SystemExit("periodic record count disagrees with payload metadata")

    total = Fraction(0)
    total_abs = Fraction(0)
    dyadic_total = Fraction(0)
    dyadic_abs = Fraction(0)
    off_orbit_total = Fraction(0)
    off_orbit_abs = Fraction(0)
    dyadic_records = 0
    off_orbit_records = 0
    base_totals: dict[int, Fraction] = defaultdict(Fraction)
    value_by_pair: dict[tuple[int, int], Fraction] = {}

    for record in records:
        q = int(record["q"])
        q2 = int(record["q2"])
        value = record_value(record)
        total += value
        total_abs += abs(value)
        value_by_pair[(q, q2)] = value
        base = dyadic_base(q, q2)
        if base is None:
            off_orbit_records += 1
            off_orbit_total += value
            off_orbit_abs += abs(value)
        else:
            dyadic_records += 1
            dyadic_total += value
            dyadic_abs += abs(value)
            base_totals[base] += value

    payload_total = Fraction(int(periodic["total_num"]), int(periodic["total_den"]))
    if total != payload_total:
        raise SystemExit("periodic record sum disagrees with payload total")
    if any(
        value <= 0
        for pair, value in value_by_pair.items()
        if dyadic_base(*pair) is not None
    ):
        raise SystemExit("found a non-positive dyadic-orbit record")

    symmetry_mismatches = []
    for (q, q2), value in value_by_pair.items():
        if dyadic_base(q, q2) is None:
            continue
        if value_by_pair.get((q2, q)) != value:
            symmetry_mismatches.append((q, q2))

    active_support = int(zero["active_support_card"])
    full_block_pairs = int(zero["full_block_ordered_pairs"])
    zero_records = int(zero["ordered_zero_records"])
    if full_block_pairs != zero_records + len(records):
        raise SystemExit("zero/nonzero periodic-main coverage is inconsistent")

    boundary_signed = parse_boundary_fraction(boundary_text, "active_signed_q")
    boundary_abs = parse_boundary_fraction(boundary_text, "active_abs_q")

    print("X0 certificate structural audit")
    print(f"  X                                      = {periodic['X']}")
    print(f"  active modulus support                 = {active_support}")
    print(f"  ordered pairs with a full block        = {full_block_pairs}")
    print(f"  full-block zero records                = {zero_records}")
    print(f"  full-block nonzero records             = {len(records)}")
    print()
    print("Periodic-main split")
    print(f"  exact signed total                     = {decimal(total)}")
    print(f"  exact absolute total                   = {decimal(total_abs)}")
    print(f"  dyadic alias records                   = {dyadic_records}")
    print(f"  dyadic alias signed/absolute total     = {decimal(dyadic_total)}")
    print(f"  dyadic share of absolute mass          = {percent(dyadic_abs, total_abs)}%")
    print(f"  off-orbit records                      = {off_orbit_records}")
    print(f"  off-orbit signed total                 = {decimal(off_orbit_total)}")
    print(f"  off-orbit absolute total               = {decimal(off_orbit_abs)}")
    print(f"  off-orbit signed/dyadic ratio          = {percent(abs(off_orbit_total), dyadic_abs)}%")
    print(f"  dyadic orientation mismatches          = {len(symmetry_mismatches)}")
    print()

    print("Odd-core localization inside the dyadic alias total")
    for base, value in sorted(base_totals.items(), key=lambda item: abs(item[1]), reverse=True)[:12]:
        print(
            f"  r={base:<5d} value={decimal(value, 12):>20s} "
            f"share={percent(abs(value), dyadic_abs):>13s}%"
        )
    for cutoff in (7, 25, 50, 100, 250, 500, 1000):
        subtotal = sum((abs(value) for base, value in base_totals.items() if base <= cutoff), Fraction(0))
        print(f"  cumulative r <= {cutoff:<4d}              = {percent(subtotal, dyadic_abs)}%")
    print()

    print("Exact low-mode Gram reconstruction")
    for base, def_name in LOW_MODE_DIAGONAL_DEFS.items():
        diagonal = parse_lean_rat_def(lean_text, def_name)
        periodic_pair = base_totals[base]
        boundary_pair = 2 * LOW_MODE_BOUNDARY_PER_ORIENTATION[base]
        reconstructed = periodic_pair + boundary_pair
        expected = 2 * diagonal
        if reconstructed != expected:
            raise SystemExit(f"low-mode reconstruction failed at r={base}")
        print(
            f"  r={base}: periodic={decimal(periodic_pair, 12)} "
            f"boundary={decimal(boundary_pair, 12)} "
            f"total=2*diagonal={decimal(expected, 12)}"
        )
    print()

    print("Non-dyadic exact factorization payload (row five excluded)")
    for key in (
        "record_count",
        "class_count",
        "lcm_fiber_count",
        "dyadic_orbit_count",
        "nontrivial_dyadic_orbit_count",
        "mean_product_mismatch_count",
        "dyadic_weight_mismatch_count",
        "lcm_total_mismatch_count",
        "exact_totals_match",
    ):
        print(f"  {key:<38s} = {lcm_payload[key]}")
    print()

    print("Active boundary")
    print(f"  exact signed total                     = {decimal(boundary_signed)}")
    print(f"  exact absolute total                   = {decimal(boundary_abs)}")
    print(
        "  absolute signed/variation ratio        = "
        f"{percent(abs(boundary_signed), boundary_abs)}%"
    )


if __name__ == "__main__":
    main()
