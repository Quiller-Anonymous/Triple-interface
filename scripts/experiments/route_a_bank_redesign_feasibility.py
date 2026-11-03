"""Route A bank-redesign feasibility audit.

This script reproduces the current PSB main lower profile at X0 and two
independent error allowances from the definitions used by Lean.  It is a
diagnostic, not a proof.  The structural fixed-bank obstruction is proved in
`RouteAFixedBankObstruction.lean`.

Only the Python standard library is required.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path


X0 = 1_000_000
H = 10_000
Q0 = 30_000
Q_LARGE = 13
SIGMA_ENVELOPE_KAPPA = 4.089173283623e-4
MINOR_ZERO_MODE_LOWER = 47.0 / 50.0
G_FORMULA_TRANSPORT = (14.0 / 13.0) ** 4
ZERO_MODE_C3 = 4.0


def even_window_card(x: int, h: int) -> int:
    """Number of even integers in the inclusive interval [x, x + h]."""
    return (x + h) // 2 - (x - 1) // 2


def totients_and_divisor_counts(limit: int) -> tuple[list[int], list[int]]:
    """Return phi(n) and tau(n) for 0 <= n <= limit."""
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for n in range(p, limit + 1, p):
                phi[n] -= phi[n] // p

    tau = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for n in range(d, limit + 1, d):
            tau[n] += 1
    return phi, tau


def lx_mean_square_upper_core_collapsed(limit: int = Q0) -> float:
    """Evaluate `LXMeanSquareUpperCoreCollapsed` from its Lean definition."""
    phi, tau = totients_and_divisor_counts(limit)
    weighted_tau_prefix = [0.0] * (limit + 1)
    for n in range(1, limit + 1):
        weighted_tau_prefix[n] = weighted_tau_prefix[n - 1] + tau[n] / n

    terms = []
    for r in range(1, limit + 1):
        lower = max(1, (Q_LARGE + r - 1) // r)
        upper = limit // r
        if lower > upper:
            continue
        inner = (weighted_tau_prefix[upper] - weighted_tau_prefix[lower - 1]) / r
        terms.append(phi[r] * inner * inner)
    return math.fsum(terms)


def route_visible_window_norm_floor(x: int) -> float:
    return (1.0 / 800.0) / math.log(x + H) ** 2


def route_a_psb_main_lower_profile(x: int) -> float:
    """Evaluate `routeAPSBSSMainLowerProfile` from the Lean definitions."""
    card = even_window_card(x, H)
    ucut = H + (H + 99) // 100
    k_full_zero = 1.0 / ucut
    geometric_window = (
        MINOR_ZERO_MODE_LOWER
        * ((1.0 / (2 * H + 1)) * (1.0 / math.log(x))) ** 2
        * k_full_zero
    )
    floor = route_visible_window_norm_floor(x)
    geometric_baseline = card * floor**2 * geometric_window
    main_scale = (800.0 * SIGMA_ENVELOPE_KAPPA) * floor
    return main_scale * geometric_baseline


def route_a_budget_record(x: int = X0) -> dict[str, object]:
    card = even_window_card(x, H)
    floor = route_visible_window_norm_floor(x)
    lx_core = lx_mean_square_upper_core_collapsed()

    # Lean definitions in Q0MinorGFormulaRouteABookkeeping and
    # Q0MinorGFormulaKernelBudgetPerTerm, with delta_weightSplit = 1.
    kernel_mass = 2.0 * (8.0 * 23.0**2 + 64.0 * lx_core) + 2.0 * 9.0
    g_core_budget = ((H + 1.0) / H) * kernel_mass
    g_c2 = G_FORMULA_TRANSPORT * g_core_budget

    main = route_a_psb_main_lower_profile(x)
    g_mean_allowance = floor * math.sqrt(card * g_c2 * H / x)
    zero_mode_c3_allowance = floor * math.sqrt(
        card * ZERO_MODE_C3 / (H * Q0**2)
    )

    return {
        "status": {
            "current_psb_budget_closes": False,
            "fixed_bank_uniform_positive_mean_possible": False,
            "growing_bank_dyadic_coverage_proved": True,
            "short_window_pair_coverage_proved": False,
            "safe_to_replace_live_bank": False,
        },
        "parameters": {
            "X": x,
            "H": H,
            "Q0": Q0,
            "q_large": Q_LARGE,
            "even_window_card": card,
        },
        "source_values": {
            "route_visible_window_norm_floor": floor,
            "route_a_psb_main_lower_profile": main,
            "lx_mean_square_upper_core_collapsed": lx_core,
            "kernel_mass_nz_parity_upper_route_a_const": kernel_mass,
            "g_formula_core_budget_const": g_core_budget,
            "g_formula_c2": g_c2,
            "g_formula_mean_allowance": g_mean_allowance,
            "zero_mode_c3_allowance": zero_mode_c3_allowance,
        },
        "ratios": {
            "g_allowance_over_main": g_mean_allowance / main,
            "zero_mode_allowance_over_main": zero_mode_c3_allowance / main,
        },
        "conclusion": (
            "The current positive-mean comparison fails numerically by many orders "
            "of magnitude, independently of the formal fixed-bank obstruction."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--X", type=int, default=X0)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    record = route_a_budget_record(args.X)
    rendered = json.dumps(record, indent=2, sort_keys=True)
    print(rendered)
    if args.output is not None:
        args.output.write_text(rendered + "\n", encoding="ascii")

    values = record["source_values"]
    assert isinstance(values, dict)
    assert values["zero_mode_c3_allowance"] > values["route_a_psb_main_lower_profile"]
    assert values["g_formula_mean_allowance"] > values["route_a_psb_main_lower_profile"]


if __name__ == "__main__":
    main()
