#!/usr/bin/env python3
"""Explore the Stage 4 fixed-target four-point Mobius correlation.

This is a falsification and structure-discovery experiment.  It freezes one
explicit admissible smooth partition for the exact Stage 4 Type-III roster; it
does not claim that finite observations prove a uniform asymptotic estimate.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class RosterEntry:
    m: int
    r: int
    p: int
    weight: float


def smooth_step(x: float) -> float:
    """A C-infinity step equal to 0 at x <= 0 and 1 at x >= 1."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    log_left = -1.0 / x
    log_right = -1.0 / (1.0 - x)
    exponent = log_right - log_left
    if exponent >= 700.0:
        return 0.0
    if exponent <= -700.0:
        return 1.0
    return 1.0 / (1.0 + math.exp(exponent))


def dyadic_cutoff(t: float) -> float:
    """A fixed theta in C_c^infinity((1/2, 2)) with dyadic sum one."""

    def chi(y: float) -> float:
        if y <= 1.0:
            return 1.0
        if y >= 2.0:
            return 0.0
        return 1.0 - smooth_step(y - 1.0)

    return max(0.0, chi(t) - chi(2.0 * t))


def product_cutoff(t: float) -> float:
    """A fixed nonnegative C-infinity cutoff on (1/4, 5/4)."""
    if not 0.25 < t < 1.25:
        return 0.0
    z = (t - 0.25) * (1.25 - t)
    return math.exp(4.0 - 1.0 / z)


def validate_dyadic_partition() -> float:
    max_error = 0.0
    for numerator in range(-80, 81):
        t = 2.0 ** (numerator / 17.0)
        total = math.fsum(dyadic_cutoff(t / (2.0**j)) for j in range(-20, 21))
        max_error = max(max_error, abs(total - 1.0))
    return max_error


def mobius_sieve(limit: int) -> list[int]:
    mu = [0] * (limit + 1)
    mu[1] = 1
    primes: list[int] = []
    composite = [False] * (limit + 1)
    for n in range(2, limit + 1):
        if not composite[n]:
            primes.append(n)
            mu[n] = -1
        for p in primes:
            value = n * p
            if value > limit:
                break
            composite[value] = True
            if n % p == 0:
                mu[value] = 0
                break
            mu[value] = -mu[n]
    return mu


def smallest_prime_factors(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    if limit >= 1:
        spf[1] = 1
    for p in range(2, math.isqrt(limit) + 1):
        if spf[p] != p:
            continue
        for value in range(p * p, limit + 1, p):
            if spf[value] == value:
                spf[value] = p
    return spf


def integer_nth_root_floor(value: int, degree: int) -> int:
    """Return floor(value^(1/degree)) without floating-point boundary errors."""
    estimate = max(1, int(value ** (1.0 / degree)))
    while (estimate + 1) ** degree <= value:
        estimate += 1
    while estimate**degree > value:
        estimate -= 1
    return estimate


def distinct_prime_factors(n: int, spf: list[int]) -> list[int]:
    factors: list[int] = []
    while n > 1:
        p = spf[n]
        factors.append(p)
        while n % p == 0:
            n //= p
    return factors


def support_bounds(x: int, u: int, a_scale: int, m: int) -> tuple[int, int]:
    """Exact integer support of theta(a/A_j) omega(am/X) with a > U."""
    lower = max(u + 1, a_scale // 2 + 1, x // (4 * m) + 1)
    upper = min(2 * a_scale - 1, (5 * x - 1) // (4 * m))
    return lower, upper


def central_block_indices(x: int, factor: float) -> list[int]:
    target = x ** 0.75
    lower = target / factor
    upper = target * factor
    base = math.floor(math.log2(target))
    return [
        j
        for j in range(base - 4, base + 6)
        if lower <= 2**j < upper
    ]


def roster_for_block(
    x: int,
    u: int,
    v: int,
    a_scale: int,
    spf: list[int],
) -> dict[int, list[RosterEntry]]:
    min_a = max(u + 1, a_scale // 2 + 1)
    max_m = (5 * x - 1) // (4 * min_a)
    roster: dict[int, list[RosterEntry]] = defaultdict(list)
    for m in range(1, max_m + 1):
        lower, upper = support_bounds(x, u, a_scale, m)
        if lower > upper:
            continue
        large_primes = [p for p in distinct_prime_factors(m, spf) if p > v]
        if len(large_primes) != 1:
            continue
        p = large_primes[0]
        r = m // p
        # This is the primitive prime-cofactor roster from Investigation 12.
        if r <= 0 or r >= v:
            continue
        r_box = 1 << (r.bit_length() - 1)
        roster[r_box].append(RosterEntry(m=m, r=r, p=p, weight=math.log(p)))
    return dict(sorted(roster.items()))


def representation_records(
    x: int,
    n_target: int,
    u: int,
    left_scale: int,
    right_scale: int,
    m: int,
    n: int,
    n_weight: float,
    mu: list[int],
) -> list[tuple[int, int, float]]:
    left_lo, left_hi = support_bounds(x, u, left_scale, m)
    right_lo, right_hi = support_bounds(x, u, right_scale, n)
    if left_lo > left_hi or right_lo > right_hi:
        return []
    residue = (n_target * pow(m, -1, n)) % n
    a = left_lo + (residue - left_lo) % n
    records: list[tuple[int, int, float]] = []
    while a <= left_hi:
        remaining = n_target - m * a
        if remaining % n == 0:
            b = remaining // n
            if right_lo <= b <= right_hi and mu[a] != 0 and mu[b] != 0:
                value = (
                    n_weight
                    * mu[a]
                    * mu[b]
                    * dyadic_cutoff(a / left_scale)
                    * product_cutoff(m * a / x)
                    * dyadic_cutoff(b / right_scale)
                    * product_cutoff(n * b / x)
                )
                if value != 0.0:
                    records.append((a, b, value))
        a += n
    return records


def square_minus_diagonal(values: Iterable[float]) -> float:
    values = list(values)
    return math.fsum(values) ** 2 - math.fsum(value * value for value in values)


def disjoint_offdiagonal_sum(
    records_by_n: dict[int, list[tuple[int, int, float]]],
    *,
    absolute: bool,
) -> float:
    totals: list[float] = []
    endpoint_total: dict[int, float] = defaultdict(float)
    endpoint_squares: dict[int, float] = defaultdict(float)
    pair_total: dict[tuple[int, int], float] = defaultdict(float)
    pair_squares: dict[tuple[int, int], float] = defaultdict(float)

    for records in records_by_n.values():
        local_endpoints: dict[int, float] = defaultdict(float)
        local_pairs: dict[tuple[int, int], float] = defaultdict(float)
        local_total = 0.0
        for a, b, raw_value in records:
            if a == b:
                continue
            value = abs(raw_value) if absolute else raw_value
            local_total += value
            local_endpoints[a] += value
            local_endpoints[b] += value
            local_pairs[(min(a, b), max(a, b))] += value
        totals.append(local_total)
        for endpoint, value in local_endpoints.items():
            endpoint_total[endpoint] += value
            endpoint_squares[endpoint] += value * value
        for pair, value in local_pairs.items():
            pair_total[pair] += value
            pair_squares[pair] += value * value

    unrestricted = square_minus_diagonal(totals)
    share_endpoint = math.fsum(
        endpoint_total[key] ** 2 - endpoint_squares[key]
        for key in endpoint_total
    )
    share_both = math.fsum(
        pair_total[key] ** 2 - pair_squares[key]
        for key in pair_total
    )
    result = unrestricted - share_endpoint + share_both
    if absolute and result < 0.0 and abs(result) < 1e-8 * max(1.0, unrestricted):
        return 0.0
    return result


def brute_disjoint_sum(
    records_by_n: dict[int, list[tuple[int, int, float]]],
    *,
    absolute: bool,
) -> float:
    total = 0.0
    for n1, records1 in records_by_n.items():
        for n2, records2 in records_by_n.items():
            if n1 == n2:
                continue
            for a1, b1, value1 in records1:
                for a2, b2, value2 in records2:
                    if len({a1, b1, a2, b2}) != 4:
                        continue
                    term = value1 * value2
                    total += abs(term) if absolute else term
    return total


def analyze_block_pair(
    *,
    x: int,
    n_target: int,
    u: int,
    left_j: int,
    right_j: int,
    left_r: int,
    right_r: int,
    left_roster: list[RosterEntry],
    right_roster: list[RosterEntry],
    mu: list[int],
    brute_limit: int,
) -> dict[str, float | int | bool]:
    left_scale = 2**left_j
    right_scale = 2**right_j
    second_moment = 0.0
    diagonal = 0.0
    generic = 0.0
    generic_abs = 0.0
    primitive_sum = 0.0
    record_count = 0
    coprime_pairs = 0
    brute_checks = 0
    brute_max_error = 0.0

    for m_entry in left_roster:
        records_by_n: dict[int, list[tuple[int, int, float]]] = {}
        h_m = 0.0
        for n_entry in right_roster:
            if math.gcd(m_entry.m, n_entry.m) != 1:
                continue
            coprime_pairs += 1
            records = representation_records(
                x,
                n_target,
                u,
                left_scale,
                right_scale,
                m_entry.m,
                n_entry.m,
                n_entry.weight,
                mu,
            )
            records_by_n[n_entry.m] = records
            sigma_weighted = math.fsum(value for _, _, value in records)
            h_m += sigma_weighted
            diagonal += sigma_weighted * sigma_weighted
            record_count += len(records)

        second_moment += h_m * h_m
        primitive_sum += m_entry.weight * h_m
        generic_m = disjoint_offdiagonal_sum(records_by_n, absolute=False)
        generic_abs_m = disjoint_offdiagonal_sum(records_by_n, absolute=True)
        generic += generic_m
        generic_abs += generic_abs_m

        local_records = sum(len(records) for records in records_by_n.values())
        if local_records <= brute_limit:
            brute_checks += 1
            brute_value = brute_disjoint_sum(records_by_n, absolute=False)
            brute_abs = brute_disjoint_sum(records_by_n, absolute=True)
            brute_max_error = max(
                brute_max_error,
                abs(brute_value - generic_m),
                abs(brute_abs - generic_abs_m),
            )

    collision = second_moment - diagonal - generic
    first_weight_square = math.fsum(entry.weight**2 for entry in left_roster)
    cauchy_slack = first_weight_square * second_moment - primitive_sum**2
    b_scale = x ** 0.25
    log_x = math.log(x)
    threshold_log3 = x * x / (b_scale * log_x**3)
    threshold_log5 = x * x / (b_scale * log_x**5)
    return {
        "left_j": left_j,
        "right_j": right_j,
        "left_r_box": left_r,
        "right_r_box": right_r,
        "left_roster_size": len(left_roster),
        "right_roster_size": len(right_roster),
        "coprime_pair_count": coprime_pairs,
        "record_count": record_count,
        "primitive_sum": primitive_sum,
        "second_moment": second_moment,
        "diagonal": diagonal,
        "collision": collision,
        "generic": generic,
        "generic_absolute_envelope": generic_abs,
        "cancellation_ratio": abs(generic) / generic_abs if generic_abs else 0.0,
        "generic_over_log3_threshold": generic / threshold_log3,
        "generic_over_log5_threshold": generic / threshold_log5,
        "absolute_over_log3_threshold": generic_abs / threshold_log3,
        "cauchy_slack": cauchy_slack,
        "identity_error": second_moment - diagonal - collision - generic,
        "brute_checked_m": brute_checks,
        "brute_max_error": brute_max_error,
    }


def even_targets(x: int, count: int, mode: str, seed: int) -> list[int]:
    lower = x if x % 2 == 0 else x + 1
    upper = 2 * x
    if count <= 1:
        return [lower]
    if mode == "random":
        steps = (upper - lower) // 2
        if count > steps + 1:
            raise ValueError("target count exceeds the available even targets")
        indexes = {0, steps}
        generator = random.Random(seed + x)
        while len(indexes) < count:
            indexes.add(generator.randrange(steps + 1))
        return [lower + 2 * index for index in sorted(indexes)]

    targets: list[int] = []
    for index in range(count):
        value = round(lower + index * (upper - lower) / (count - 1))
        if value % 2:
            value += 1
        targets.append(min(value, upper))
    return sorted(set(targets))


def integer_factorization(value: int) -> list[list[int]]:
    factors: list[list[int]] = []
    remainder = value
    divisor = 2
    while divisor * divisor <= remainder:
        if remainder % divisor:
            divisor = 3 if divisor == 2 else divisor + 2
            continue
        exponent = 0
        while remainder % divisor == 0:
            remainder //= divisor
            exponent += 1
        factors.append([divisor, exponent])
        divisor = 3 if divisor == 2 else divisor + 2
    if remainder > 1:
        factors.append([remainder, 1])
    return factors


def analyze_scale(
    x: int,
    *,
    target_count: int,
    target_mode: str,
    target_seed: int,
    central_factor: float,
    brute_limit: int,
) -> dict:
    u = max(2, integer_nth_root_floor(x, 6))
    v = u
    block_indices = central_block_indices(x, central_factor)
    max_a = max(2 * (2**j) - 1 for j in block_indices)
    mu = mobius_sieve(max_a)

    max_m = max(
        (5 * x - 1) // (4 * max(u + 1, 2 ** (j - 1) + 1))
        for j in block_indices
    )
    spf = smallest_prime_factors(max_m)
    rosters = {
        j: roster_for_block(x, u, v, 2**j, spf)
        for j in block_indices
    }

    target_results: list[dict] = []
    for n_target in even_targets(x, target_count, target_mode, target_seed):
        blocks: list[dict] = []
        for left_j in block_indices:
            for right_j in block_indices:
                for left_r, left_entries in rosters[left_j].items():
                    for right_r, right_entries in rosters[right_j].items():
                        blocks.append(
                            analyze_block_pair(
                                x=x,
                                n_target=n_target,
                                u=u,
                                left_j=left_j,
                                right_j=right_j,
                                left_r=left_r,
                                right_r=right_r,
                                left_roster=left_entries,
                                right_roster=right_entries,
                                mu=mu,
                                brute_limit=brute_limit,
                            )
                        )
        nonempty = [block for block in blocks if block["record_count"]]
        envelope_sum = math.fsum(
            float(block["generic_absolute_envelope"]) for block in nonempty
        )
        generic_sum = math.fsum(float(block["generic"]) for block in nonempty)
        max_envelope = max(
            (float(block["generic_absolute_envelope"]) for block in nonempty),
            default=0.0,
        )
        material_blocks = [
            block
            for block in nonempty
            if float(block["generic_absolute_envelope"]) >= 0.01 * max_envelope
        ]
        top_signed_block = max(
            nonempty,
            key=lambda block: float(block["generic_over_log3_threshold"]),
            default=None,
        )
        target_results.append(
            {
                "N": n_target,
                "factorization": integer_factorization(n_target),
                "blocks": blocks,
                "nonempty_blocks": len(nonempty),
                "primitive_sum_total": math.fsum(
                    float(block["primitive_sum"]) for block in blocks
                ),
                "generic_sum": generic_sum,
                "generic_absolute_envelope_sum": envelope_sum,
                "aggregate_cancellation_ratio": (
                    abs(generic_sum) / envelope_sum if envelope_sum else 0.0
                ),
                "max_generic_over_log3_threshold": max(
                    (float(block["generic_over_log3_threshold"]) for block in nonempty),
                    default=0.0,
                ),
                "max_generic_over_log5_threshold": max(
                    (float(block["generic_over_log5_threshold"]) for block in nonempty),
                    default=0.0,
                ),
                "max_absolute_over_log3_threshold": max(
                    (float(block["absolute_over_log3_threshold"]) for block in nonempty),
                    default=0.0,
                ),
                "max_cancellation_ratio": max(
                    (float(block["cancellation_ratio"]) for block in nonempty),
                    default=0.0,
                ),
                "max_material_cancellation_ratio": max(
                    (
                        float(block["cancellation_ratio"])
                        for block in material_blocks
                    ),
                    default=0.0,
                ),
                "top_signed_block": (
                    {
                        key: top_signed_block[key]
                        for key in (
                            "left_j",
                            "right_j",
                            "left_r_box",
                            "right_r_box",
                            "record_count",
                            "generic_over_log3_threshold",
                            "generic_over_log5_threshold",
                            "absolute_over_log3_threshold",
                            "cancellation_ratio",
                        )
                    }
                    if top_signed_block
                    else None
                ),
            }
        )

    roster_summary = {
        str(j): {
            str(r_box): [asdict(entry) for entry in entries]
            for r_box, entries in roster.items()
        }
        for j, roster in rosters.items()
    }
    return {
        "X": x,
        "A": x ** 0.75,
        "B": x ** 0.25,
        "U": u,
        "V": v,
        "central_factor": central_factor,
        "target_mode": target_mode,
        "target_seed": target_seed,
        "block_indices": block_indices,
        "rosters": roster_summary,
        "targets": target_results,
    }


def print_summary(result: dict) -> None:
    for scale in result["scales"]:
        print(
            f"[scale] X={scale['X']} U=V={scale['U']} "
            f"j={scale['block_indices']}"
        )
        for target in scale["targets"]:
            print(
                f"[target] N={target['N']} blocks={target['nonempty_blocks']} "
                f"max_G/log3={target['max_generic_over_log3_threshold']:.6g} "
                f"max_G/log5={target['max_generic_over_log5_threshold']:.6g} "
                f"max_abs/log3={target['max_absolute_over_log3_threshold']:.6g} "
                f"aggregate_ratio={target['aggregate_cancellation_ratio']:.6g} "
                f"material_ratio={target['max_material_cancellation_ratio']:.6g}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--x", type=int, action="append", dest="scales")
    parser.add_argument("--target-count", type=int, default=5)
    parser.add_argument("--target-mode", choices=("grid", "random"), default="grid")
    parser.add_argument("--target-seed", type=int, default=20261103)
    parser.add_argument("--central-factor", type=float, default=2.0)
    parser.add_argument("--brute-limit", type=int, default=350)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    scales = args.scales or [1_000_000]
    if any(x < 256 for x in scales):
        raise SystemExit("all scales must be at least 256")
    if args.central_factor <= 1.0:
        raise SystemExit("--central-factor must be greater than one")

    result = {
        "experiment": "Stage 4 fixed-target four-point atlas",
        "status": "finite exploratory evidence only",
        "dyadic_partition_max_error": validate_dyadic_partition(),
        "frozen_model": {
            "U_and_V": "floor(X^(1/6))",
            "A_j": "2^j with X^(3/4)/factor <= A_j < factor*X^(3/4)",
            "theta": "chi(t)-chi(2t), chi=1 below 1 and C-infinity to 0 at 2",
            "omega": "exp(4-1/((t-1/4)(5/4-t))) on (1/4,5/4)",
            "primitive_roster": "m=r*p, p>V prime, r<V, w_m=log(p)",
        },
        "scales": [
            analyze_scale(
                x,
                target_count=args.target_count,
                target_mode=args.target_mode,
                target_seed=args.target_seed,
                central_factor=args.central_factor,
                brute_limit=args.brute_limit,
            )
            for x in scales
        ],
    }
    if result["dyadic_partition_max_error"] > 1e-12:
        raise RuntimeError("the frozen dyadic partition failed its numerical check")
    print_summary(result)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        print(f"[output] {args.output}")


if __name__ == "__main__":
    main()
