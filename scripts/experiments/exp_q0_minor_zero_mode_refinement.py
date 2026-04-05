#!/usr/bin/env python3
"""
Zero-mode refinement diagnostic on the exact route-visible minor object.

By the current route-visible diagnostics, the post-geometric residual is
overwhelmingly concentrated in the zero mode. This script studies that `t = 0`
channel directly on a dense even window `N in [X, X+H]`.

It compares:

1. geometric-only fit
2. geometric + singular-series modulation
3. geometric + smooth quadratic correction

The point is to test whether the remaining zero-mode discrepancy is primarily
arithmetic (singular-series-like) or merely a smooth envelope error.
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


UCUT = H + (H + 99) // 100


def k_full(k: int) -> float:
    if abs(k) > H:
        return 0.0
    return max(1.0 - abs(k) / float(UCUT), 0.0) / float(UCUT)


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


def even_window(X: int, step: int) -> list[int]:
    start = X if X % 2 == 0 else X + 1
    return list(range(start, X + H + 1, max(2, step if step % 2 == 0 else step + 1)))


def fit_scalar(actual: list[float], model: list[float]) -> tuple[float, float, float]:
    denom = dot(model, model)
    beta = 0.0 if denom == 0.0 else dot(actual, model) / denom
    residual = [a - beta * m for a, m in zip(actual, model)]
    full_energy = dot(actual, actual)
    residual_energy = dot(residual, residual)
    captured_energy = max(full_energy - residual_energy, 0.0)
    return beta, captured_energy, residual_energy


def fit_multicolumn(actual: list[float], columns: list[list[float]]) -> tuple[list[float], float, float]:
    gram = [[dot(c1, c2) for c2 in columns] for c1 in columns]
    rhs = [dot(col, actual) for col in columns]
    coeffs = solve_linear_system(gram, rhs)
    approx = [0.0] * len(actual)
    for coeff, col in zip(coeffs, columns):
        for i, x in enumerate(col):
            approx[i] += coeff * x
    residual = [a - b for a, b in zip(actual, approx)]
    full_energy = dot(actual, actual)
    residual_energy = dot(residual, residual)
    captured_energy = max(full_energy - residual_energy, 0.0)
    return coeffs, captured_energy, residual_energy


def fit_loglog_exponent(xs: list[int], ys: list[float]) -> float:
    lx = [math.log(float(x)) for x in xs]
    ly = [math.log(float(y)) for y in ys]
    mx = sum(lx) / len(lx)
    my = sum(ly) / len(ly)
    num = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    den = sum((a - mx) * (a - mx) for a in lx)
    return num / den


def smallest_prime_factors(n: int) -> list[int]:
    spf = list(range(n + 1))
    for i in range(2, int(math.isqrt(n)) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def odd_prime_divisors(n: int, spf: list[int]) -> list[int]:
    out: list[int] = []
    last = 0
    while n > 1:
        p = spf[n]
        if p != last and p > 2:
            out.append(p)
        last = p
        n //= p
    return out


def singular_series_shape(n: int, spf: list[int]) -> float:
    val = 1.0
    for p in odd_prime_divisors(n, spf):
        val *= (p - 1.0) / (p - 2.0)
    return val


def centered(values: list[float]) -> list[float]:
    mean = sum(values) / len(values)
    return [x - mean for x in values]


def corr(u: list[float], v: list[float]) -> float:
    nu = math.sqrt(max(dot(u, u), 0.0))
    nv = math.sqrt(max(dot(v, v), 0.0))
    if nu <= 1e-30 or nv <= 1e-30:
        return 0.0
    return dot(u, v) / (nu * nv)


def main() -> None:
    parser = argparse.ArgumentParser(description="Zero-mode refinement diagnostic on a dense even window.")
    parser.add_argument("--X-list", type=str, default="100000,300000,1000000")
    parser.add_argument("--step", type=int, default=2, help="even step size in N across [X, X+H]")
    args = parser.parse_args()

    Xs = parse_x_list(args.X_list)
    max_n = max(Xs) + H
    spf = smallest_prime_factors(max_n)

    geom_residual_rows: list[tuple[int, float]] = []
    ss_residual_rows: list[tuple[int, float]] = []
    poly_residual_rows: list[tuple[int, float]] = []

    for X in Xs:
        Ns = even_window(X, args.step)
        prime_by_s = sum_by_s(X)
        geom_by_s = sum_by_s_uniform_fast(X)
        mu_q0, phi_q0 = mobius_phi_sieve(Q0)
        backend = WeightBackend(kind="exact", X=X, mu_q0=mu_q0, phi_q0=phi_q0)
        w0 = backend.minor_weight(0)

        exact = [q0_norm_factor(N) * prime_by_s.get(N, 0.0) * w0 for N in Ns]
        geom = [q0_norm_factor(N) * geom_by_s.get(N, 0.0) * w0 for N in Ns]

        ss_shape = [singular_series_shape(N, spf) for N in Ns]
        ss_centered = centered(ss_shape)
        u = [(N - (X + H / 2.0)) / float(H) for N in Ns]

        beta_geom, captured_geom, resid_geom = fit_scalar(exact, geom)
        geom_resid_vec = [a - beta_geom * g for a, g in zip(exact, geom)]

        ss_columns = [
            geom,
            [g * s for g, s in zip(geom, ss_centered)],
        ]
        ss_coeffs, captured_ss, resid_ss = fit_multicolumn(exact, ss_columns)

        poly_columns = [
            geom,
            [g * x for g, x in zip(geom, u)],
            [g * (x * x) for g, x in zip(geom, u)],
        ]
        poly_coeffs, captured_poly, resid_poly = fit_multicolumn(exact, poly_columns)

        geom_residual_rows.append((X, math.sqrt(resid_geom)))
        ss_residual_rows.append((X, math.sqrt(resid_ss)))
        poly_residual_rows.append((X, math.sqrt(resid_poly)))

        total_norm = math.sqrt(dot(exact, exact))
        print(f"== X={X:,} ==")
        print(f"dense_even_window_size={len(Ns)}")
        print(f"zeroMode dense norm = {total_norm:.12e}")
        print()
        print("-- geometric fit --")
        print(f"beta = {beta_geom:.12e}")
        print(f"capture = {100.0 * captured_geom / (captured_geom + resid_geom):.6f}%")
        print(f"residual_norm = {math.sqrt(resid_geom):.12e}")
        print()
        print("-- geometric + singular-series fit --")
        print(f"coeff_geom = {ss_coeffs[0]:.12e}")
        print(f"coeff_ss   = {ss_coeffs[1]:.12e}")
        print(f"capture = {100.0 * captured_ss / (captured_ss + resid_ss):.6f}%")
        print(f"residual_norm = {math.sqrt(resid_ss):.12e}")
        print()
        print("-- geometric + quadratic-envelope fit --")
        print(f"coeff_geom = {poly_coeffs[0]:.12e}")
        print(f"coeff_lin  = {poly_coeffs[1]:.12e}")
        print(f"coeff_quad = {poly_coeffs[2]:.12e}")
        print(f"capture = {100.0 * captured_poly / (captured_poly + resid_poly):.6f}%")
        print(f"residual_norm = {math.sqrt(resid_poly):.12e}")
        print()
        print("-- residual diagnostics --")
        print(f"corr(geom residual, ss_shape) = {corr(geom_resid_vec, ss_centered):.6f}")
        max_idx = max(range(len(geom_resid_vec)), key=lambda i: abs(geom_resid_vec[i]))
        print(
            f"max residual at N={Ns[max_idx]} : "
            f"{geom_resid_vec[max_idx]:.12e}"
        )
        print()

    if len(Xs) >= 2:
        xs = [x for x, _ in geom_residual_rows]
        geom_resids = [y for _, y in geom_residual_rows]
        ss_resids = [y for _, y in ss_residual_rows]
        poly_resids = [y for _, y in poly_residual_rows]
        print("== Log-Log Exponents ==")
        print(f"geom-only residual exponent         = {fit_loglog_exponent(xs, geom_resids):.6f}")
        print(f"geom+singular-series residual exp   = {fit_loglog_exponent(xs, ss_resids):.6f}")
        print(f"geom+quadratic residual exp         = {fit_loglog_exponent(xs, poly_resids):.6f}")


if __name__ == "__main__":
    main()
