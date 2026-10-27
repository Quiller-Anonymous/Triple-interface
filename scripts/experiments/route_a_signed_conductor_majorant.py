#!/usr/bin/env python3
"""Evaluate signed-conductor Type-I majorants in log space.

This is a numerical audit of equations (18)--(23) in the 2026-10-27 specialist
note.  It does not prove the external character estimates used to derive those
equations and is not part of the Lean dependency chain.  The ``localized``
variant keeps the same signed small-conductor terms and multiplies only the
large-conductor term by 3/2, matching the Lean factor-18 represented-fiber
branch in place of the factor-12 complete-fiber branch.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass


LOG_TEN = math.log(10.0)


def logaddexp(left: float, right: float) -> float:
    """Return log(exp(left) + exp(right)) without avoidable overflow."""
    high = max(left, right)
    low = min(left, right)
    if high == math.inf:
        return high
    if high == -math.inf:
        return high
    return high + math.log1p(math.exp(low - high))


@dataclass(frozen=True)
class MajorantAudit:
    route: str
    log_log_n: float
    log_terms: dict[str, float]
    log_total: float
    log_nu_times_v: float

    @property
    def total(self) -> float:
        return math.exp(self.log_total)

    @property
    def log10_total(self) -> float:
        return self.log_total / LOG_TEN


def evaluate_majorant(log_log_n: float, route: str = "complete") -> MajorantAudit:
    """Evaluate the six normalized error terms using P_N <= 4 log log N."""
    s = log_log_n
    if s <= 0:
        raise ValueError("log_log_n must be positive")
    if route not in {"complete", "localized"}:
        raise ValueError(f"unknown route: {route}")

    ell = math.exp(s)
    correction = 30.0 * s * math.exp(-s)
    if correction >= 1.0:
        raise ValueError("the prescribed v = log N - 30 log log N is not positive")

    log_v = s + math.log1p(-correction)
    log_r = math.log(0.5) + 10.0 * log_v
    log_k = 1.5 * log_v
    p_n = 4.0 * s
    a_r = 1.0 + log_r
    c_zero = 3.2e-8

    # nu = min(100 / (sqrt(K) log(K)^2), 1 / (4.0904 log(R))).
    log_nu_one = math.log(100.0) - 0.5 * log_k - 2.0 * math.log(log_k)
    log_nu_two = -math.log(2.0 * 2.0452) - math.log(log_r)
    log_nu_times_v = min(log_nu_one, log_nu_two) + log_v
    nu_times_v = (
        math.inf if log_nu_times_v > 700.0 else math.exp(log_nu_times_v)
    )

    log_terms: dict[str, float] = {}
    log_terms["noncoprime_prime_power"] = -(2.0 / 3.0) * ell + 2.0 * s
    log_terms["induced_character"] = (
        -(2.0 / 3.0) * ell
        + 3.0 * s
        - math.log(3.0)
        - math.log(math.log(2.0))
    )

    high_first = math.log(4.0) - log_r
    log_27_plus = logaddexp(math.log(27.0), math.log(5.0 / 3.0) + s)
    high_second = log_27_plus - ell / 6.0
    large_prefactor = 196.0 if route == "complete" else 294.0
    log_terms["large_conductor"] = (
        math.log(large_prefactor)
        + 5.5 * s
        + logaddexp(high_first, high_second)
    )

    log_terms["small_early"] = (
        math.log(48.0 * p_n) + log_r - 28.0 * s
    )

    regular_first = math.log(c_zero) - 8.0 * log_v
    regular_second = math.log(2.0) - nu_times_v
    log_terms["small_regular"] = (
        math.log(72.0 * p_n)
        + s
        + math.log(a_r)
        + logaddexp(regular_first, regular_second)
    )

    log_log_r = math.log(log_r)
    log_terms["exceptional_character"] = (
        math.log(2304.0 * p_n)
        + s
        + math.log(a_r)
        + 2.0 * math.log(log_log_r)
        - log_k
    )

    log_total = -math.inf
    for value in log_terms.values():
        log_total = logaddexp(log_total, value)

    return MajorantAudit(route, s, log_terms, log_total, log_nu_times_v)


def printable_value(log_value: float) -> str:
    if log_value > -700.0:
        return f"{math.exp(log_value):.12e}"
    return f"10^({log_value / LOG_TEN:.6e})"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--log-log-n",
        type=float,
        default=100.0,
        help="s = log(log(N)); the specialist's verified range starts at 100",
    )
    parser.add_argument(
        "--route",
        choices=("complete", "localized"),
        default="complete",
        help=(
            "complete uses the factor-12 full-fiber large branch; localized "
            "uses the factor-18 represented-fiber large branch"
        ),
    )
    parser.add_argument("--target", type=float, default=1e-9)
    parser.add_argument(
        "--check",
        action="store_true",
        help="exit unsuccessfully unless the total is below --target",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    audit = evaluate_majorant(args.log_log_n, args.route)
    if args.json:
        payload = {
            "route": audit.route,
            "log_log_n": audit.log_log_n,
            "terms_log10": {
                name: value / LOG_TEN for name, value in audit.log_terms.items()
            },
            "total": audit.total,
            "total_log10": audit.log10_total,
            "target": args.target,
            "passes_target": audit.log_total < math.log(args.target),
            "log_nu_times_v": audit.log_nu_times_v,
        }
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"route = {audit.route}")
        print(f"log(log(N)) = {audit.log_log_n:g}")
        for name, value in audit.log_terms.items():
            print(f"{name:28s} {printable_value(value):>22s}")
        print(f"{'total':28s} {printable_value(audit.log_total):>22s}")
        print(f"total log10                 {audit.log10_total:22.12f}")
        print(f"target                      {args.target:22.12e}")

    if args.check and not audit.log_total < math.log(args.target):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
