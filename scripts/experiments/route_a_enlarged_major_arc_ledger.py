#!/usr/bin/env python3
"""Combine proved rows in the enlarged-major-arc paper ledger.

This script performs only decimal bookkeeping. It deliberately refuses to
produce a successful reserve while a row is missing, grouped, or unproved.
It does not establish any analytic input.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from pathlib import Path


getcontext().prec = 80


def decimal_field(record: dict[str, object], name: str) -> Decimal:
    value = record.get(name)
    if not isinstance(value, str):
        raise ValueError(f"{name} must be a decimal string")
    return Decimal(value)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    data = json.loads(args.input.read_text())
    q_max = int(data["Q"])
    rows = data.get("rows")
    if not isinstance(rows, list):
        raise ValueError("rows must be a list")

    seen: set[int] = set()
    model_lower = Decimal(0)
    model_error = Decimal(0)
    problems: list[str] = []

    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            problems.append(f"row {index} is not an object")
            continue
        q = row.get("q")
        if not isinstance(q, int):
            problems.append(f"row {index} does not represent one integer q")
            continue
        if q < 1 or q > q_max:
            problems.append(f"q={q} is outside 1..{q_max}")
            continue
        if q in seen:
            problems.append(f"q={q} is duplicated")
            continue
        seen.add(q)
        if row.get("status") != "proved":
            problems.append(f"q={q} has status {row.get('status')!r}, not 'proved'")
            continue
        try:
            model_lower += decimal_field(row, "model_lower_fraction")
            error = decimal_field(row, "model_error_upper_fraction")
        except ValueError as exc:
            problems.append(f"q={q}: {exc}")
            continue
        if error < 0:
            problems.append(f"q={q} has a negative error allowance")
            continue
        model_error += error

    missing = sorted(set(range(1, q_max + 1)) - seen)
    if missing:
        problems.append(f"missing q rows: {missing}")

    active_main = decimal_field(data, "active_main_lower_fraction")
    type_i_error = decimal_field(data, "type_i_error_upper_fraction")
    prime_power = decimal_field(data, "prime_power_upper_fraction")
    reserve = active_main + model_lower - type_i_error - model_error - prime_power

    print(f"P={data['P']} Q={q_max} base_commit={data['base_commit']}")
    print(f"active_main_lower       {active_main}")
    print(f"major_model_lower       {model_lower}")
    print(f"type_i_error_upper      {type_i_error}")
    print(f"major_model_error_upper {model_error}")
    print(f"prime_power_upper       {prime_power}")
    print(f"reserve_lower           {reserve}")

    if problems:
        print("ledger_status            INCOMPLETE")
        for problem in problems:
            print(f"problem: {problem}")
        return 2 if args.check else 0

    if reserve <= 0:
        print("ledger_status            COMPLETE_BUT_NONPOSITIVE")
        return 1 if args.check else 0

    print("ledger_status            COMPLETE_POSITIVE")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
