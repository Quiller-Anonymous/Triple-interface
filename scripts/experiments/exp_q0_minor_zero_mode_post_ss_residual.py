#!/usr/bin/env python3
"""
Post-singular-series residual diagnostic for the zero mode.

This script starts from the dense-window zero-mode model

  exact ≈ geom + geom * singular_series

and studies the remaining residual after the best geometric + singular-series fit.

It compares two classes of secondary explanation:

1. smooth drift:
   geom * u, geom * u^2
2. small-prime arithmetic features:
   geom * 1_{p | N} for small odd primes p, centered over the window,
   plus geom * omega_odd(N)

The goal is to decide whether the tiny post-singular-series discrepancy looks like
smooth envelope error, residual local arithmetic, or neither.
"""

from __future__ import annotations

import argparse
import math

from exp_q0_minor_singularity_exact_harness import (
    H,
    Q0,
    WeightBackend,
    dot,
    mobius_phi_sieve,
    q0_norm_factor,
    solve_linear_system,
    sum_by_s,
)
from exp_q0_minor_zero_mode_refinement import (
    corr,
    even_window,
    fit_loglog_exponent,
    fit_multicolumn,
    k_full,
    smallest_prime_factors,
    singular_series_shape,
)


UCUT = H + (H + 99) // 100


def sum_by_s_uniform_fast(X: int) -> dict[int, float]:
    lo = X // 2 - H
    hi = X // 2 + H
    s_lo = 2 * lo
    s_hi = 2 * hi

    even = [0.0]
    odd = [0.0]
    acc_even = 0.0
    acc_odd = 0.0
    for d in range(0, H + 1):
        val = k_full(d)
        if d % 2 == 0:
            acc_even += val
            even.append(acc_even)
        else:
            acc_odd += val
            odd.append(acc_odd)

    def parity_sum(M: int, parity: int) -> float:
        if M < 0:
            return 0.0
        if parity == 0:
            return even[M // 2 + 1]
        return odd[(M + 1) // 2]

    out: dict[int, float] = {}
    k0 = k_full(0)
    for s in range(s_lo, s_hi + 1):
        M = min(H, s - s_lo, s_hi - s)
        parity = s & 1
        total = k0 if parity == 0 else 0.0
        if M >= (2 if parity == 0 else 1):
            total += 2.0 * parity_sum(M, parity)
            if parity == 0:
                total -= 2.0 * k0
        out[s] = total
    return out


def parse_x_list(spec: str) -> list[int]:
    out: list[int] = []
    for piece in spec.split(","):
        piece = piece.strip()
        if piece:
            out.append(int(piece))
    if not out:
        raise SystemExit("empty --X-list")
    return out


def centered(values: list[float]) -> list[float]:
    mean = sum(values) / len(values)
    return [x - mean for x in values]


def odd_prime_divisor_count(n: int, spf: list[int]) -> int:
    count = 0
    last = 0
    while n > 1:
        p = spf[n]
        if p != last and p > 2:
            count += 1
        last = p
        n //= p
    return count


def feature_report(
    *,
    label: str,
    base_residual: list[float],
    feature: list[float],
) -> tuple[str, float, float]:
    coeff, captured, residual = fit_multicolumn(base_residual, [feature])
    total = captured + residual
    capture_ratio = 0.0 if total == 0.0 else captured / total
    return label, coeff[0], capture_ratio


def main() -> None:
    parser = argparse.ArgumentParser(description="Post-singular-series zero-mode residual diagnostic.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2)
    parser.add_argument("--small-primes", type=str, default="3,5,7,11,13")
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    small_primes = [int(x.strip()) for x in args.small_primes.split(",") if x.strip()]
    max_n = max(Xs) + H
    spf = smallest_prime_factors(max_n)

    base_residual_rows: list[tuple[int, float]] = []
    smooth_residual_rows: list[tuple[int, float]] = []
    arith_residual_rows: list[tuple[int, float]] = []
    joint_residual_rows: list[tuple[int, float]] = []

    for X in Xs:
        Ns = even_window(X, args.step)
        prime_by_s = sum_by_s(X)
        geom_by_s = sum_by_s_uniform_fast(X)
        mu_q0, phi_q0 = mobius_phi_sieve(Q0)
        backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
        w0 = backend.minor_weight(0)

        exact = [q0_norm_factor(N) * prime_by_s.get(N, 0.0) * w0 for N in Ns]
        geom = [q0_norm_factor(N) * geom_by_s.get(N, 0.0) * w0 for N in Ns]

        ss_shape = centered([singular_series_shape(N, spf) for N in Ns])
        u = [(N - (X + H / 2.0)) / float(H) for N in Ns]

        base_columns = [
            geom,
            [g * s for g, s in zip(geom, ss_shape)],
        ]
        base_coeffs, base_captured, base_residual = fit_multicolumn(exact, base_columns)
        base_approx = [
            base_coeffs[0] * geom[i] + base_coeffs[1] * geom[i] * ss_shape[i]
            for i in range(len(Ns))
        ]
        resid = [a - b for a, b in zip(exact, base_approx)]

        smooth_columns = [
            [geom[i] * u[i] for i in range(len(Ns))],
            [geom[i] * u[i] * u[i] for i in range(len(Ns))],
        ]
        smooth_coeffs, smooth_captured, smooth_residual = fit_multicolumn(resid, smooth_columns)

        omega_centered = centered([float(odd_prime_divisor_count(N, spf)) for N in Ns])
        arith_columns = [[geom[i] * omega_centered[i] for i in range(len(Ns))]]
        for p in small_primes:
            ind_centered = centered([1.0 if N % p == 0 else 0.0 for N in Ns])
            arith_columns.append([geom[i] * ind_centered[i] for i in range(len(Ns))])
        arith_coeffs, arith_captured, arith_residual = fit_multicolumn(resid, arith_columns)

        joint_columns = smooth_columns + arith_columns
        joint_coeffs, joint_captured, joint_residual = fit_multicolumn(resid, joint_columns)

        base_residual_rows.append((X, math.sqrt(base_residual)))
        smooth_residual_rows.append((X, math.sqrt(smooth_residual)))
        arith_residual_rows.append((X, math.sqrt(arith_residual)))
        joint_residual_rows.append((X, math.sqrt(joint_residual)))

        total_norm = math.sqrt(dot(exact, exact))
        resid_norm = math.sqrt(dot(resid, resid))
        print(f"== X={X:,} ==")
        print(f"dense_even_window_size={len(Ns)}")
        print(f"zeroMode dense norm = {total_norm:.12e}")
        print()
        print("-- base fit: geometric + singular-series --")
        print(f"coeff_geom = {base_coeffs[0]:.12e}")
        print(f"coeff_ss   = {base_coeffs[1]:.12e}")
        print(f"base residual norm = {resid_norm:.12e}")
        print(f"base residual energy ratio = {100.0 * base_residual / (base_captured + base_residual):.6f}%")
        print()
        print("-- smooth refinement on residual --")
        print(f"coeff_lin  = {smooth_coeffs[0]:.12e}")
        print(f"coeff_quad = {smooth_coeffs[1]:.12e}")
        print(f"capture of residual = {100.0 * smooth_captured / (smooth_captured + smooth_residual):.6f}%")
        print(f"remaining residual norm = {math.sqrt(smooth_residual):.12e}")
        print()
        print("-- arithmetic refinement on residual --")
        labels = ["omega_odd"] + [f"1_{{{p}|N}}" for p in small_primes]
        for label, coeff in zip(labels, arith_coeffs):
            print(f"{label:>12} coeff = {coeff:.12e}")
        print(f"capture of residual = {100.0 * arith_captured / (arith_captured + arith_residual):.6f}%")
        print(f"remaining residual norm = {math.sqrt(arith_residual):.12e}")
        print()
        print("-- joint smooth + arithmetic refinement --")
        print(f"capture of residual = {100.0 * joint_captured / (joint_captured + joint_residual):.6f}%")
        print(f"remaining residual norm = {math.sqrt(joint_residual):.12e}")
        print()
        print("-- correlations with base residual --")
        print(f"corr(u)               = {corr(resid, smooth_columns[0]):.6f}")
        print(f"corr(u^2)             = {corr(resid, smooth_columns[1]):.6f}")
        print(f"corr(omega_odd)       = {corr(resid, arith_columns[0]):.6f}")
        for p, col in zip(small_primes, arith_columns[1:]):
            print(f"corr(1_{{{p}|N}})      = {corr(resid, col):.6f}")
        print()

    if len(Xs) >= 2:
        xs = [x for x, _ in base_residual_rows]
        base_vals = [y for _, y in base_residual_rows]
        smooth_vals = [y for _, y in smooth_residual_rows]
        arith_vals = [y for _, y in arith_residual_rows]
        joint_vals = [y for _, y in joint_residual_rows]
        print("== Log-Log Exponents ==")
        print(f"base post-SS residual exponent     = {fit_loglog_exponent(xs, base_vals):.6f}")
        print(f"smooth-refined residual exponent   = {fit_loglog_exponent(xs, smooth_vals):.6f}")
        print(f"arith-refined residual exponent    = {fit_loglog_exponent(xs, arith_vals):.6f}")
        print(f"joint-refined residual exponent    = {fit_loglog_exponent(xs, joint_vals):.6f}")


if __name__ == "__main__":
    main()
