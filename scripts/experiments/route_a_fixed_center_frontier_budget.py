#!/usr/bin/env python3
"""Reproduce the deterministic arithmetic in the latest Route A frontier budget.

This script checks only decimal arithmetic derived from the paper-level inputs in
RouteAOneLargePrimeCompletionAudit.md. It does not prove those analytic inputs.
"""

from decimal import Decimal, getcontext


getcontext().prec = 60

reserve = Decimal("0.708")
sufficient_error = Decimal("0.707")
strategic_error = Decimal("0.599")
small_cofactor_cost = Decimal("0.001609")
log_three_halves = Decimal(3).ln() - Decimal(2).ln()
factor_two_cost = 2 * log_three_halves


def show(name: str, value: Decimal) -> None:
    print(f"{name}={value}")


show("log_three_halves", log_three_halves)
show("factor_two_cost", factor_two_cost)
show("factor_two_deficit_against_reserve", factor_two_cost - reserve)
show("largest_uniform_factor_from_reserve", reserve / log_three_halves)
show("required_improvement_from_factor_two", 2 - reserve / log_three_halves)
show("factor_corresponding_to_0_707", sufficient_error / log_three_halves)
show("factor_corresponding_to_0_599", strategic_error / log_three_halves)
show("reserve_after_small_cofactor_cost", reserve - small_cofactor_cost)

assert factor_two_cost > reserve
assert reserve / log_three_halves < 2
assert reserve - small_cofactor_cost == Decimal("0.706391")
