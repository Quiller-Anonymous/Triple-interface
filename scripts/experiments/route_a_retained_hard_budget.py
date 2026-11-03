#!/usr/bin/env python3
"""Check the paper constants for the retained q=1,2 hard-residual estimate.

The calculation uses only logarithms at N >= exp(exp(100)).  It verifies that conservative
prefix bounds for Lambda - TypeI imply an absolute retained-hard allowance below 0.49 N.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext


def compute(log_log_n: Decimal) -> dict[str, object]:
    getcontext().prec = 80

    one = Decimal(1)
    two = Decimal(2)
    log_n = log_log_n.exp()
    log_two = two.ln()
    log_u_lower = log_n / Decimal(3) - log_two
    log_n_over_u_upper = Decimal(2) * log_n / Decimal(3) + log_two
    log_ratio_with_constant = (log_n_over_u_upper + one) / log_u_lower

    harmonic = one / Decimal(69)
    smoothing = one / Decimal(389)

    # Prefix of the unmodulated Type-I coefficient minus x.
    q1_core = smoothing / log_u_lower + harmonic * log_ratio_with_constant

    # Odd-support Mobius sums are the ordinary sums convolved with the powers of two.  Splitting
    # those powers at u^(1/100) costs a factor 2/(99/100) in the main part; the tail is negligible.
    odd_harmonic = two * harmonic / (Decimal(99) / Decimal(100) * log_u_lower)
    odd_smoothing = two * smoothing / (Decimal(99) / Decimal(100) * log_u_lower)
    odd_prefix_core = (
        odd_smoothing + odd_harmonic * (log_n_over_u_upper + one)
    ) / two

    q2_core = q1_core + two * odd_prefix_core

    # Terms suppressed from the displayed core constants.
    pnt_relative_log_upper = (
        Decimal("9.4").ln()
        + Decimal("1.515") * log_n.ln()
        - Decimal("0.8274") * log_n.sqrt()
    )
    factorial_error_relative_log_upper = (
        -Decimal(2) * log_n / Decimal(3) + (one + two * log_n).ln()
    )
    parity_tail_log_upper = -log_u_lower / Decimal(100)
    endpoint_error_relative_log_upper = (
        Decimal(1_000_001).ln() + (one + log_n).ln() - log_n
    )

    # Rounded prefix budgets absorb every suppressed term by an enormous margin.
    q1_budget = Decimal("0.03")
    q2_budget = Decimal("0.09")
    psi_over_n_budget = Decimal("1.01")
    pi_upper = Decimal("3.142")

    # Integrating the Abel bounds, rather than multiplying by their endpoint maxima, gives
    # 2(1+pi)/N on the q=1 arc and (1+pi/2)/N on the q=2 arc.
    retained_hard_fraction = psi_over_n_budget * (
        two * (one + pi_upper) * q1_budget
        + (one + pi_upper / two) * q2_budget
    )

    checks = {
        "q1_core_lt_0_03": q1_core < q1_budget,
        "q2_core_lt_0_09": q2_core < q2_budget,
        "pnt_remainder_below_exp_minus_300": pnt_relative_log_upper < Decimal(-300),
        "factorial_remainder_below_exp_minus_300": (
            factorial_error_relative_log_upper < Decimal(-300)
        ),
        "parity_tail_below_exp_minus_300": parity_tail_log_upper < Decimal(-300),
        "endpoint_remainder_below_exp_minus_300": (
            endpoint_error_relative_log_upper < Decimal(-300)
        ),
        "retained_hard_fraction_lt_0_49": retained_hard_fraction < Decimal("0.49"),
    }

    return {
        "log_log_n": str(log_log_n),
        "q1_core_fraction": str(q1_core),
        "odd_prefix_core_fraction": str(odd_prefix_core),
        "q2_core_fraction": str(q2_core),
        "retained_hard_fraction": str(retained_hard_fraction),
        "safe_retained_hard_fraction": "0.49",
        "active_main_fraction_from_kernel_audit": "0.9",
        "restored_margin_before_complementary_hard": "0.41",
        "checks": checks,
        "all_checks": all(checks.values()),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log-log-n", default="100")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    result = compute(Decimal(args.log_log_n))
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.check and not result["all_checks"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
