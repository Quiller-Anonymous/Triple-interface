#!/usr/bin/env python3
"""Check the paper constants in the Route A active-main kernel argument.

This is a feasibility calculation, not a proof artifact.  It evaluates only logarithms of the
astronomical quantities at the frozen threshold N >= exp(exp(100)); no huge integer is built.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext


def compute(log_log_n: Decimal) -> dict[str, str | bool]:
    getcontext().prec = 80

    one = Decimal(1)
    two = Decimal(2)
    log_n = log_log_n.exp()
    log_two = two.ln()

    # u = floor(N^(1/3)) satisfies N^(1/3)/2 <= u <= N^(1/3).
    log_u_lower = log_n / Decimal(3) - log_two
    log_n_over_u_upper = Decimal(2) * log_n / Decimal(3) + log_two
    log_ratio = log_n_over_u_upper / log_u_lower

    # Split the kernel at D = floor(u^(1/100)).  On d <= D, u/d >= u^(99/100).
    split_fraction = Decimal(1) / Decimal(100)
    base_log_fraction = one - split_fraction
    harmonic_bound = one / Decimal(69)
    smoothing_bound = one / Decimal(389)
    kernel_mass_factor = Decimal(6)

    harmonic_error_over_p = (
        kernel_mass_factor * harmonic_bound / (base_log_fraction * log_u_lower)
    )
    smoothing_error_over_p = (
        kernel_mass_factor * smoothing_bound / (base_log_fraction * log_u_lower)
    )
    profile_loss_over_p = (
        harmonic_error_over_p * log_n_over_u_upper + smoothing_error_over_p
    )

    # P_N / singularSeries(N) <= 1 / C2, using C2 > 0.66.
    c2_lower = Decimal("0.66")
    profile_loss_over_singular = profile_loss_over_p / c2_lower

    # Rankin tail: sum_{d>D}|h_N(d)| <= D^(-1/2) sum |h_N(d)| sqrt(d).
    # The latter moment is at most exp(8 + 7 sqrt(1 + log(N)/log(2))).
    kernel_tail_log_upper = (
        log_two / two
        - split_fraction * log_u_lower / two
        + Decimal(8)
        + Decimal(7) * (one + log_n / log_two).sqrt()
    )

    # The discarded k < u range is bounded by 6 u (1 + log u) log u.
    low_range_loss_ratio_log_upper = (
        Decimal(6).ln()
        - Decimal(2) * log_n / Decimal(3)
        + (one + log_n / Decimal(3)).ln()
        + (log_n / Decimal(3)).ln()
    )
    cutoff_ratio_log_upper = -Decimal(2) * log_n / Decimal(3)
    endpoint_ratio_log_upper = Decimal(1_000_001).ln() - log_n

    singular_floor = Decimal(2) * c2_lower
    high_profile_floor_without_tail = singular_floor * (
        one - profile_loss_over_singular
    )

    checks = {
        "log_ratio_le_2_01": log_ratio <= Decimal("2.01"),
        "kernel_tail_below_exp_minus_300": kernel_tail_log_upper <= Decimal(-300),
        "low_range_below_exp_minus_300_N": low_range_loss_ratio_log_upper <= Decimal(-300),
        "cutoff_below_exp_minus_300_N": cutoff_ratio_log_upper <= Decimal(-300),
        "endpoint_below_exp_minus_300_N": endpoint_ratio_log_upper <= Decimal(-300),
        "high_profile_floor_gt_0_95": high_profile_floor_without_tail > Decimal("0.95"),
    }

    return {
        "log_log_n": str(log_log_n),
        "log_n": str(log_n),
        "log_u_lower": str(log_u_lower),
        "log_n_over_u_upper": str(log_n_over_u_upper),
        "log_ratio_upper": str(log_ratio),
        "harmonic_error_over_p": str(harmonic_error_over_p),
        "smoothing_error_over_p": str(smoothing_error_over_p),
        "profile_loss_over_p": str(profile_loss_over_p),
        "profile_loss_over_singular": str(profile_loss_over_singular),
        "kernel_tail_log_upper": str(kernel_tail_log_upper),
        "low_range_loss_ratio_log_upper": str(low_range_loss_ratio_log_upper),
        "high_profile_floor_without_tail": str(high_profile_floor_without_tail),
        "safe_active_main_fraction": "0.9",
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
