#!/usr/bin/env python3
"""Audit the revised localized short Type-I paper majorant in log space.

This script implements the declaration-specific bounds in the 2026-10-27
weighted-tail note.  In particular, it keeps the inverse-conductor weight
inside the Akbary--Hambrook sum and splits the small conductors at

    D = floor((log(N) - 30 log log(N))^7 / 2).

It is a reproducibility check, not a proof of the cited analytic estimates and
not part of the Lean dependency chain.  All reported quantities are normalized
by N.  The calculation avoids constructing N = exp(exp(s)).
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass


LOG_TEN = math.log(10.0)


def logaddexp(left: float, right: float) -> float:
    """Return log(exp(left) + exp(right)) without avoidable underflow."""
    if left == -math.inf:
        return right
    if right == -math.inf:
        return left
    high = max(left, right)
    low = min(left, right)
    return high + math.log1p(math.exp(low - high))


def logsumexp(values: list[float]) -> float:
    total = -math.inf
    for value in values:
        total = logaddexp(total, value)
    return total


@dataclass(frozen=True)
class RevisedTypeIAudit:
    log_log_n: float
    log_terms: dict[str, float]
    log_total: float
    log_v: float
    log_nu_v: float
    range_checks: dict[str, bool]

    @property
    def total(self) -> float:
        return math.exp(self.log_total)

    @property
    def log10_total(self) -> float:
        return self.log_total / LOG_TEN


def evaluate(log_log_n: float) -> RevisedTypeIAudit:
    """Evaluate conservative upper envelopes from the revised paper argument."""
    s = log_log_n
    if s < 100.0:
        raise ValueError("the revised paper range requires log(log(N)) >= 100")

    ell = math.exp(s)
    correction = 30.0 * s * math.exp(-s)
    if not 0.0 < correction < 1.0:
        raise ValueError("v = log(N) - 30 log log(N) is not positive")

    # v = ell - 30s, represented through log(v).
    log_v = s + math.log1p(-correction)
    v = math.exp(log_v)
    p_n = 4.0 * s
    log_log_r_upper = math.log(10.0 * s)

    # K = v^(3/2) and nu as in the revised exceptional-zero split.
    log_k = 1.5 * log_v
    log_nu_one = math.log(100.0) - 0.5 * log_k - 2.0 * math.log(log_k)
    log_nu_two = -math.log(167.0 * s)
    log_nu = min(log_nu_one, log_nu_two)
    log_nu_v = log_nu + log_v
    nu_v = math.exp(log_nu_v) if log_nu_v < 700.0 else math.inf

    terms: dict[str, float] = {}

    # Equation (10), after P_N <= 4s.
    terms["principal"] = (
        math.log(451.2)
        + math.log(s)
        + 2.515 * s
        - 0.8274 * math.exp(s / 2.0)
    )

    # Equations (19) and (22), evaluated before the coarser display (33).
    log_epsilon_parts = [
        math.log(2.0) - 30.0 * s,
        math.log(208.0 * s) + 19.0 * s - nu_v,
        math.log(20.0 * s) - 18.0 * log_v,
    ]
    log_epsilon = logsumexp(log_epsilon_parts)
    # D <= v^7/2.
    terms["small_low_regular"] = (
        math.log(72.0 * p_n)
        + s
        + 7.0 * log_v
        - math.log(2.0)
        + log_epsilon
    )

    # Equation (25).  Use D >= v^7/3 and R <= v^10/2.
    log_f_mid_parts = [
        math.log(12.0) - 7.0 * log_v,
        math.log(2.0) + 10.0 * log_v - ell / 2.0,
        math.log(18.0 / math.sqrt(2.0)) + 5.0 * log_v - ell / 3.0,
        math.log(5.0)
        + math.log1p(math.log(1.5) + 3.0 * log_v)
        - ell / 6.0,
    ]
    log_f_mid_over_n = math.log(49.0) + 3.5 * s + logsumexp(log_f_mid_parts)
    terms["small_mid"] = (
        math.log(48.0 * p_n)
        + s
        + math.log(log_log_r_upper)
        + log_f_mid_over_n
    )

    # Equation (24), with log log R <= log(10s).
    terms["exceptional_character"] = (
        math.log(384.0 * p_n)
        + s
        + 2.0 * math.log(log_log_r_upper)
        - log_k
    )

    # Equations (31)--(32), using R >= v^10/3 and u <= N^(1/3).
    log_large_bracket = logsumexp(
        [
            math.log(12.0) - 10.0 * log_v,
            logaddexp(math.log(27.0), math.log(5.0 / 3.0) + s)
            - ell / 6.0,
        ]
    )
    terms["large_represented"] = math.log(343.0) + 5.5 * s + log_large_bracket

    # Existing induced and noncoprime envelopes from equation (39).
    terms["induced_character"] = (
        -(2.0 / 3.0) * ell
        + 3.0 * s
        - math.log(3.0 * math.log(2.0))
    )
    terms["noncoprime"] = math.log(2.0) - ell / 3.0 + 3.0 * s

    log_total = logsumexp(list(terms.values()))
    range_checks = {
        "v_ge_half_ell": correction <= 0.5,
        "nu_v_ge_100s": log_nu_v >= math.log(100.0 * s),
        "K_gt_30": log_k > math.log(30.0),
        "D_lt_R": 7.0 * log_v - math.log(2.0) < 10.0 * log_v - math.log(3.0),
        "revised_budget_lt_5e-15": log_total < math.log(5.0e-15),
        "legacy_budget_lt_8_48e-12": log_total < math.log(8.48e-12),
    }
    return RevisedTypeIAudit(s, terms, log_total, log_v, log_nu_v, range_checks)


def printable(log_value: float) -> str:
    if log_value > -700.0:
        return f"{math.exp(log_value):.12e}"
    return f"10^({log_value / LOG_TEN:.6e})"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log-log-n", type=float, default=100.0)
    parser.add_argument("--target", type=float, default=5.0e-15)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--scan-through",
        type=float,
        default=None,
        help="also sample integer s values through this endpoint and check monotone decrease",
    )
    args = parser.parse_args()

    audit = evaluate(args.log_log_n)
    scan_monotone = True
    if args.scan_through is not None:
        previous = audit.log_total
        start = math.ceil(args.log_log_n) + 1
        stop = math.floor(args.scan_through)
        for sample in range(start, stop + 1):
            current = evaluate(float(sample)).log_total
            if current > previous:
                scan_monotone = False
            previous = current

    if args.json:
        print(
            json.dumps(
                {
                    "log_log_n": audit.log_log_n,
                    "terms_log10": {
                        name: value / LOG_TEN for name, value in audit.log_terms.items()
                    },
                    "total": audit.total,
                    "total_log10": audit.log10_total,
                    "target": args.target,
                    "passes_target": audit.log_total < math.log(args.target),
                    "range_checks": audit.range_checks,
                    "sampled_monotone": scan_monotone,
                },
                indent=2,
                sort_keys=True,
            )
        )
    else:
        print(f"log(log(N)) = {audit.log_log_n:g}")
        for name, value in audit.log_terms.items():
            print(f"{name:28s} {printable(value):>22s}")
        print(f"{'total':28s} {printable(audit.log_total):>22s}")
        print(f"total log10                 {audit.log10_total:22.12f}")
        print(f"target                      {args.target:22.12e}")
        for name, passed in audit.range_checks.items():
            print(f"check {name:35s} {'PASS' if passed else 'FAIL'}")
        if args.scan_through is not None:
            print(f"check sampled_monotone{'':24s} {'PASS' if scan_monotone else 'FAIL'}")

    if args.check:
        if audit.log_total >= math.log(args.target):
            return 1
        if not all(audit.range_checks.values()) or not scan_monotone:
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
