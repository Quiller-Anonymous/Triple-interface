#!/usr/bin/env python3
"""
Exact audit of the unified odd-surface coprime squarefree periodic-main branch.

This script mirrors the current Lean surface:

  centeredNormalizedSigmaTruncPeriodicMainCoeffSupportedCoprimeOddModulusUnifiedPairSumUpToQ0

and compares:

  1. the exact signed unified odd-surface sum
  2. the exact absolute-value sum with the exact multiplicity weight
  3. the crude 3 * |c(a)c(b)| * |K(a,b)| majorant
  4. the endpoint constants and one-block majorants

It also splits the signed odd-surface kernel into the exact Lean pieces:

  - coefficient mismatch
  - density mismatch
  - remainder

and reports signed value, absolute value, cancellation ratio, and swap-symmetry
diagnostics for each piece.

Normalization note:
  normalizedSigmaTruncSummandRealCoeff q
    = 1 / (phi(q)^2 * (2 * C2))
on squarefree support, but the true singular-series constant C2 is not represented as a
computable exact rational in Lean. To keep the audit exact, this script factors out the
global scale (2 * C2)^(-2) and works with the scalar-free coefficient

  c_base(q) = 1 / phi(q)^2.

For convenience it also reports the surrogate normalized values obtained by taking
`C2_numeric = 1/10`, so the pair scale is exactly 25.
"""

from __future__ import annotations

import argparse
import math
from fractions import Fraction


H = 10_000
Q0 = 30_000
H1 = H + 1
C2_NUMERIC = Fraction(1, 10)
PAIR_NORMALIZATION_SURROGATE = Fraction(1, 1) / ((2 * C2_NUMERIC) ** 2)
FOCUS_ROWS = [3, 5, 7, 15]


def mobius_phi_sieve(n: int) -> tuple[list[int], list[int]]:
    mu = [0] * (n + 1)
    phi = [0] * (n + 1)
    is_comp = [False] * (n + 1)
    primes: list[int] = []
    mu[1] = 1
    phi[1] = 1
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
            phi[i] = i - 1
        for p in primes:
            ip = i * p
            if ip > n:
                break
            is_comp[ip] = True
            if i % p == 0:
                mu[ip] = 0
                phi[ip] = phi[i] * p
                break
            mu[ip] = -mu[i]
            phi[ip] = phi[i] * (p - 1)
    return mu, phi


def spf_sieve(n: int) -> list[int]:
    spf = list(range(n + 1))
    if n >= 0:
        spf[0] = 0
    if n >= 1:
        spf[1] = 1
    for i in range(2, int(math.isqrt(n)) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def factorization(n: int, spf: list[int]) -> dict[int, int]:
    out: dict[int, int] = {}
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        out[p] = e
    return out


def format_factorization(n: int, spf: list[int]) -> str:
    if n == 1:
        return "1"
    fac = factorization(n, spf)
    pieces: list[str] = []
    for p in sorted(fac):
        e = fac[p]
        if e == 1:
            pieces.append(str(p))
        else:
            pieces.append(f"{p}^{e}")
    return "*".join(pieces)


def divisors_from_factorization(fac: dict[int, int]) -> list[int]:
    divs = [1]
    for p, e in fac.items():
        cur: list[int] = []
        pe = 1
        for _ in range(e + 1):
            for d in divs:
                cur.append(d * pe)
            pe *= p
        divs = cur
    divs.sort()
    return divs


def build_squarefree_support(q0: int, mu: list[int]) -> list[int]:
    return [q for q in range(1, q0 + 1) if mu[q] != 0]


def build_odd_squarefree_support(q0: int, mu: list[int]) -> list[int]:
    return [q for q in range(1, q0 + 1) if (q % 2 == 1) and mu[q] != 0]


def even_window_points(X: int) -> list[int]:
    start = X if (X % 2 == 0) else X + 1
    return list(range(start, X + H + 1, 2))


def coeff_base(q: int, mu: list[int], phi: list[int]) -> Fraction:
    if mu[q] == 0:
        return Fraction(0, 1)
    return Fraction(1, phi[q] * phi[q])


def gcd_class_coeff(q: int, g: int, mu: list[int], phi: list[int]) -> int:
    return mu[q // g] * phi[g]


def format_fraction(fr: Fraction) -> str:
    if fr.denominator == 1:
        return str(fr.numerator)
    return f"{fr.numerator}/{fr.denominator}"


def ceil_div(n: int, d: int) -> int:
    return (n + d - 1) // d


def centered_ramanujan_pair_block_period(q: int, q2: int) -> int:
    return 2 * math.lcm(q, q2)


def main() -> None:
    ap = argparse.ArgumentParser(description="Exact unified odd-surface audit for the coprime squarefree branch.")
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--Q0", type=int, default=Q0)
    ap.add_argument("--class7-scan", action="store_true")
    ap.add_argument("--class-residue-scan", type=int)
    ap.add_argument("--residual-scan", action="store_true")
    ap.add_argument("--fixed-a-residue-scan", type=int)
    ap.add_argument("--residue-modulus", type=int)
    ap.add_argument("--fixed-a-bucket-scan", type=int)
    ap.add_argument("--fixed-a-omega-scan", type=int)
    ap.add_argument("--fixed-a-omega2-three-scan", type=int)
    ap.add_argument("--fixed-a-omega2-three-five-scan", type=int)
    ap.add_argument("--fixed-a-omega2-three-five-not-p-scan", type=int)
    ap.add_argument("--fixed-a-omega2-notthree-family-scan", type=int)
    ap.add_argument("--fixed-a-dominant-scan", type=int)
    ap.add_argument("--scan-xs", type=int, nargs="*")
    args = ap.parse_args()

    X = args.X
    q0 = args.Q0

    mu, phi = mobius_phi_sieve(q0)
    spf = spf_sieve(q0)

    coeff_support = build_squarefree_support(q0, mu)
    odd_support = build_odd_squarefree_support(q0, mu)
    odd_active_support = [a for a in odd_support if a <= H1 // 2]

    even_window = even_window_points(X)
    even_window_card = len(even_window)

    divisors_cache: dict[int, list[int]] = {}
    for q in set(odd_active_support + [1, 2]):
        divisors_cache[q] = divisors_from_factorization(factorization(q, spf))

    avg_counts: dict[int, dict[int, int]] = {}
    for q in set(odd_active_support + [1, 2]):
        counts = {g: 0 for g in divisors_cache[q]}
        for N in even_window:
            counts[math.gcd(q, N)] += 1
        avg_counts[q] = counts

    def window_average(q: int, g: int) -> Fraction:
        return Fraction(avg_counts[q][g], even_window_card)

    def odd_odd_period(a: int, b: int) -> int:
        return centered_ramanujan_pair_block_period(a, b)

    def even_block_count(a: int, b: int) -> int:
        return odd_odd_period(a, b) // 2

    def odd_odd_pair_count(a: int, b: int, g: int, h: int) -> int:
        A = a // g
        B = b // h
        return phi[A * B]

    def odd_odd_left_count(a: int, b: int, g: int) -> int:
        A = a // g
        return b * phi[A]

    def odd_odd_right_count(a: int, b: int, h: int) -> int:
        B = b // h
        return a * phi[B]

    def odd_odd_explicit_parity_correction_point(a: int, b: int, g: int, h: int) -> Fraction:
        A = a // g
        B = b // h
        return Fraction(2 * phi[A] * phi[B], 1)

    def odd_odd_coefficient_mismatch_point(a: int, b: int, g: int, h: int) -> Fraction:
        A = a // g
        B = b // h
        period = odd_odd_period(a, b)
        pair_len = ((X + period - 1) // math.lcm(g, h) + 1) - ceil_div(X, math.lcm(g, h))
        left_len = ((X + period - 1) // g + 1) - ceil_div(X, g)
        right_len = ((X + period - 1) // h + 1) - ceil_div(X, h)
        return Fraction(phi[A] * phi[B], 1) * (
            Fraction(pair_len // (A * B), 1)
            - Fraction((left_len // A) * (right_len // B), even_block_count(a, b))
        )

    def odd_odd_density_mismatch_point(a: int, b: int, g: int, h: int) -> Fraction:
        block = even_block_count(a, b)
        left_count = odd_odd_left_count(a, b, g)
        right_count = odd_odd_right_count(a, b, h)
        avg_a = window_average(a, g)
        avg_b = window_average(b, h)
        return Fraction(block, 1) * (
            Fraction(left_count, block) - avg_a
        ) * (
            Fraction(right_count, block) - avg_b
        )

    def odd_odd_full_even_block_sum(a: int, b: int, g: int, h: int) -> Fraction:
        pair_count = odd_odd_pair_count(a, b, g, h)
        left_count = odd_odd_left_count(a, b, g)
        right_count = odd_odd_right_count(a, b, h)
        avg_a = window_average(a, g)
        avg_b = window_average(b, h)
        block = even_block_count(a, b)
        return (
            Fraction(pair_count, 1)
            - avg_b * left_count
            - avg_a * right_count
            + avg_a * avg_b * block
        )

    def odd_odd_remainder_point(a: int, b: int, g: int, h: int) -> Fraction:
        return (
            odd_odd_full_even_block_sum(a, b, g, h)
            - odd_odd_explicit_parity_correction_point(a, b, g, h)
            - odd_odd_coefficient_mismatch_point(a, b, g, h)
            - odd_odd_density_mismatch_point(a, b, g, h)
        )

    def odd_odd_sector(a: int, b: int) -> Fraction:
        if a == b or math.gcd(a, b) != 1:
            return Fraction(0, 1)
        P = odd_odd_period(a, b)
        block_scalar = H1 // P
        if block_scalar == 0:
            return Fraction(0, 1)
        total = Fraction(0, 1)
        for g in divisors_cache[a]:
            cg = gcd_class_coeff(a, g, mu, phi)
            for h in divisors_cache[b]:
                ch = gcd_class_coeff(b, h, mu, phi)
                total += Fraction(cg * ch * block_scalar, 1) * odd_odd_full_even_block_sum(a, b, g, h)
        return total

    def odd_odd_piece_sector(a: int, b: int, piece: str) -> Fraction:
        if a == b or math.gcd(a, b) != 1:
            return Fraction(0, 1)
        P = odd_odd_period(a, b)
        block_scalar = H1 // P
        if block_scalar == 0:
            return Fraction(0, 1)
        if piece == "coeff":
            point_fn = odd_odd_coefficient_mismatch_point
        elif piece == "density":
            point_fn = odd_odd_density_mismatch_point
        elif piece == "remainder":
            point_fn = odd_odd_remainder_point
        else:
            raise ValueError(piece)
        total = Fraction(0, 1)
        for g in divisors_cache[a]:
            cg = gcd_class_coeff(a, g, mu, phi)
            for h in divisors_cache[b]:
                ch = gcd_class_coeff(b, h, mu, phi)
                total += Fraction(cg * ch * block_scalar, 1) * point_fn(a, b, g, h)
        return total

    def odd_odd_raw_abs_majorant(a: int, b: int) -> Fraction:
        if a == b or math.gcd(a, b) != 1:
            return Fraction(0, 1)
        total = Fraction(0, 1)
        for g in divisors_cache[a]:
            cg = gcd_class_coeff(a, g, mu, phi)
            for h in divisors_cache[b]:
                ch = gcd_class_coeff(b, h, mu, phi)
                total += abs(Fraction(cg * ch, 1) * odd_odd_full_even_block_sum(a, b, g, h))
        return total

    def multiplicity(a: int, b: int) -> int:
        return 1 + int(2 * a in coeff_support) + int(2 * b in coeff_support)

    def effective_weight_base(a: int, b: int) -> Fraction:
        return Fraction(multiplicity(a, b), 1) * coeff_base(a, mu, phi) * coeff_base(b, mu, phi)

    def periodic_main_generic(q: int, q2: int) -> Fraction:
        P = 2 * math.lcm(q, q2)
        block_scalar = H1 // P
        if block_scalar == 0:
            return Fraction(0, 1)
        even_points = [X + k for k in range(P) if (X + k) % 2 == 0]
        total = Fraction(0, 1)
        divisors_q = divisors_cache.setdefault(q, divisors_from_factorization(factorization(q, spf)))
        divisors_q2 = divisors_cache.setdefault(q2, divisors_from_factorization(factorization(q2, spf)))
        for g in divisors_q:
            avg_q = window_average(q, g)
            cg = gcd_class_coeff(q, g, mu, phi)
            for h in divisors_q2:
                avg_q2 = window_average(q2, h)
                ch = gcd_class_coeff(q2, h, mu, phi)
                pair_count = 0
                left_count = 0
                right_count = 0
                for N in even_points:
                    hit_q = (math.gcd(q, N) == g)
                    hit_q2 = (math.gcd(q2, N) == h)
                    if hit_q:
                        left_count += 1
                    if hit_q2:
                        right_count += 1
                    if hit_q and hit_q2:
                        pair_count += 1
                full_sum = (
                    Fraction(pair_count, 1)
                    - avg_q2 * left_count
                    - avg_q * right_count
                    + avg_q * avg_q2 * (P // 2)
                )
                total += Fraction(cg * ch * block_scalar, 1) * full_sum
        return total

    unified_exact = Fraction(0, 1)
    unified_abs_exact_weight = Fraction(0, 1)
    unified_abs_crude_three = Fraction(0, 1)
    combined_one_block_majorant = Fraction(0, 1)
    left_one_block_majorant = Fraction(0, 1)
    right_one_block_majorant = Fraction(0, 1)

    active_pair_count = 0
    multiplicities_seen: set[int] = set()
    max_abs_kernel = Fraction(0, 1)
    max_abs_weight = Fraction(0, 1)
    piece_names = ["coeff", "density", "remainder", "total"]
    piece_signed: dict[str, Fraction] = {k: Fraction(0, 1) for k in piece_names}
    piece_abs: dict[str, Fraction] = {k: Fraction(0, 1) for k in piece_names}
    piece_pair_values: dict[tuple[str, int, int], Fraction] = {}
    density_row_inner: dict[int, Fraction] = {}
    density_row_contrib: dict[int, Fraction] = {}
    density_row_count: dict[int, int] = {}
    density_row_abs: dict[int, Fraction] = {}
    density_row_pos_mass: dict[int, Fraction] = {}
    density_row_neg_mass: dict[int, Fraction] = {}
    density_row_terms: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {}
    density_pos_count = 0
    density_neg_count = 0
    density_zero_count = 0
    density_pos_mass = Fraction(0, 1)
    density_neg_mass = Fraction(0, 1)
    class7_signed = Fraction(0, 1)
    class7_majorant = Fraction(0, 1)
    class_residue_signed = Fraction(0, 1)
    class_residue_majorant = Fraction(0, 1)
    class_residue = args.class_residue_scan % 15 if args.class_residue_scan is not None else None

    for a in odd_active_support:
        base_a = coeff_base(a, mu, phi)
        density_inner = Fraction(0, 1)
        density_weighted = Fraction(0, 1)
        density_count = 0
        density_abs = Fraction(0, 1)
        density_row_pos = Fraction(0, 1)
        density_row_neg = Fraction(0, 1)
        row_terms: list[tuple[int, Fraction, Fraction, Fraction]] = []
        for b in odd_active_support:
            if a == b or math.gcd(a, b) != 1:
                continue
            if a * b > H1 // 2:
                continue
            active_pair_count += 1
            m = multiplicity(a, b)
            multiplicities_seen.add(m)
            base_weight = base_a * coeff_base(b, mu, phi)
            eff_weight = Fraction(m, 1) * base_weight
            coeff_piece = odd_odd_piece_sector(a, b, "coeff")
            density_piece = odd_odd_piece_sector(a, b, "density")
            remainder_piece = odd_odd_piece_sector(a, b, "remainder")
            kernel = coeff_piece + density_piece + remainder_piece
            piece_pair_values[("coeff", a, b)] = base_weight * coeff_piece
            piece_pair_values[("density", a, b)] = base_weight * density_piece
            piece_pair_values[("remainder", a, b)] = base_weight * remainder_piece
            piece_pair_values[("total", a, b)] = base_weight * kernel
            piece_signed["coeff"] += base_weight * coeff_piece
            piece_signed["density"] += base_weight * density_piece
            piece_signed["remainder"] += base_weight * remainder_piece
            piece_signed["total"] += base_weight * kernel
            piece_abs["coeff"] += abs(base_weight * coeff_piece)
            piece_abs["density"] += abs(base_weight * density_piece)
            piece_abs["remainder"] += abs(base_weight * remainder_piece)
            piece_abs["total"] += abs(base_weight * kernel)
            density_row_term = coeff_base(b, mu, phi) * density_piece
            density_inner += density_row_term
            density_weighted += base_weight * density_piece
            density_count += 1
            density_pair = base_weight * density_piece
            row_terms.append((b, coeff_base(b, mu, phi), density_piece, density_row_term))
            density_abs += abs(coeff_base(b, mu, phi) * density_piece)
            if a == 5 and b % 15 == 7:
                class7_signed += base_weight * density_piece
                class7_majorant += abs(base_weight * density_piece)
            if class_residue is not None and a == 5 and b % 15 == class_residue:
                class_residue_signed += base_weight * density_piece
                class_residue_majorant += abs(base_weight * density_piece)
            if density_pair > 0:
                density_pos_count += 1
                density_pos_mass += density_pair
                density_row_pos += density_row_term
            elif density_pair < 0:
                density_neg_count += 1
                density_neg_mass += -density_pair
                density_row_neg += -density_row_term
            else:
                density_zero_count += 1
            raw_abs = odd_odd_raw_abs_majorant(a, b)
            unified_exact += eff_weight * kernel
            unified_abs_exact_weight += abs(eff_weight * kernel)
            unified_abs_crude_three += Fraction(3, 1) * abs(base_weight * kernel)
            left_term = base_weight * raw_abs
            right_term = base_weight * raw_abs
            left_one_block_majorant += left_term
            right_one_block_majorant += right_term
            combined_one_block_majorant += left_term + right_term
            max_abs_kernel = max(max_abs_kernel, abs(kernel))
            max_abs_weight = max(max_abs_weight, abs(eff_weight))
        density_row_inner[a] = density_inner
        density_row_contrib[a] = density_weighted
        density_row_count[a] = density_count
        density_row_abs[a] = density_abs
        density_row_pos_mass[a] = density_row_pos
        density_row_neg_mass[a] = density_row_neg
        density_row_terms[a] = row_terms

    if args.class7_scan:
        ratio = float(abs(class7_signed) / class7_majorant) if class7_majorant != 0 else float("nan")
        print("Class-7 scan")
        print(f"  X = {X}")
        print(f"  T5(7) = {format_fraction(class7_signed)}")
        print(f"  T5(7) (float) = {float(class7_signed):.12g}")
        print(f"  M5(7) = {format_fraction(class7_majorant)}")
        print(f"  M5(7) (float) = {float(class7_majorant):.12g}")
        print(f"  |T5(7)| / M5(7) = {ratio:.12g}")
        return

    if class_residue is not None:
        ratio = float(abs(class_residue_signed) / class_residue_majorant) if class_residue_majorant != 0 else float("nan")
        print("Class-residue scan")
        print(f"  X = {X}")
        print(f"  residue = {class_residue}")
        print(f"  T5({class_residue}) = {format_fraction(class_residue_signed)}")
        print(f"  T5({class_residue}) (float) = {float(class_residue_signed):.12g}")
        print(f"  M5({class_residue}) = {format_fraction(class_residue_majorant)}")
        print(f"  M5({class_residue}) (float) = {float(class_residue_majorant):.12g}")
        print(f"  |T5({class_residue})| / M5({class_residue}) = {ratio:.12g}")
        return

    if args.residual_scan:
        useful_residues = {7, 9, 4, 11, 13}
        highlighted_residual = [2, 14, 6, 3]
        residual_rows = density_row_terms.get(5, [])
        residual_terms = [t for t in residual_rows if t[0] % 15 not in useful_residues]
        c5 = coeff_base(5, mu, phi)
        residual_signed = sum((c5 * term for _, _, _, term in residual_terms), Fraction(0, 1))
        residual_majorant = sum((abs(c5 * term) for _, _, _, term in residual_terms), Fraction(0, 1))
        residual_ratio = float(abs(residual_signed) / residual_majorant) if residual_majorant != 0 else float("nan")

        print("Residual bucket scan")
        print(f"  X = {X}")
        print(f"  T5,residual = {format_fraction(residual_signed)}")
        print(f"  T5,residual (float) = {float(residual_signed):.12g}")
        print(f"  |T5,residual| = {format_fraction(abs(residual_signed))}")
        print(f"  |T5,residual| (float) = {float(abs(residual_signed)):.12g}")
        print(f"  M5,residual = {format_fraction(residual_majorant)}")
        print(f"  M5,residual (float) = {float(residual_majorant):.12g}")
        print(f"  |T5,residual| / M5,residual = {residual_ratio:.12g}")
        print()

        print("Residual class breakdown")
        print("  class            signed                  abs majorant            ratio        count   nonzero")
        residual_residues = [r for r in range(15) if r not in useful_residues]
        for r in residual_residues:
            bucket = [t for t in residual_rows if t[0] % 15 == r]
            signed = sum((c5 * term for _, _, _, term in bucket), Fraction(0, 1))
            majorant = sum((abs(c5 * term) for _, _, _, term in bucket), Fraction(0, 1))
            ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
            nonzero = sum(1 for _, _, _, term in bucket if term != 0)
            print(
                f"  r={r:<2}             "
                f"{float(signed):>14.6g}  "
                f"{float(majorant):>14.6g}  "
                f"{ratio:>10.6g}  "
                f"{len(bucket):>8}  "
                f"{nonzero:>7}"
            )
        print()

        other_residual_residues = [r for r in residual_residues if r not in highlighted_residual]
        other_bucket = [t for t in residual_rows if t[0] % 15 in other_residual_residues]
        other_signed = sum((c5 * term for _, _, _, term in other_bucket), Fraction(0, 1))
        other_majorant = sum((abs(c5 * term) for _, _, _, term in other_bucket), Fraction(0, 1))
        other_ratio = float(abs(other_signed) / other_majorant) if other_majorant != 0 else float("nan")
        print("Grouped residual sub-buckets")
        for name, residues in [
            ("r=2", [2]),
            ("near0 {14,6,3}", [14, 6, 3]),
            ("other residual", other_residual_residues),
        ]:
            bucket = [t for t in residual_rows if t[0] % 15 in residues]
            signed = sum((c5 * term for _, _, _, term in bucket), Fraction(0, 1))
            majorant = sum((abs(c5 * term) for _, _, _, term in bucket), Fraction(0, 1))
            ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
            print(
                f"  {name:<16}"
                f"signed={float(signed):>14.6g}  "
                f"abs={float(majorant):>14.6g}  "
                f"ratio={ratio:>10.6g}  "
                f"residues={residues}"
            )
        return

    if args.fixed_a_residue_scan is not None:
        a = args.fixed_a_residue_scan
        if a not in density_row_terms:
            print("Fixed-a residue scan")
            print(f"  a = {a}")
            print("  row not present on active odd surface")
            return
        modulus = args.residue_modulus if args.residue_modulus is not None else 3 * a
        if modulus <= 0:
            raise ValueError("residue modulus must be positive")
        terms = density_row_terms[a]
        ca = coeff_base(a, mu, phi)
        row_signed = density_row_contrib[a]
        row_abs = sum((abs(ca * term) for _, _, _, term in terms), Fraction(0, 1))
        row_ratio = float(abs(row_signed) / row_abs) if row_abs != 0 else float("nan")

        print("Fixed-a residue scan")
        print(f"  X = {X}")
        print(f"  a = {a}")
        print(f"  modulus = {modulus}")
        print(f"  fac(a) = {format_factorization(a, spf)}")
        print(f"  c(a) = {format_fraction(ca)}")
        print(f"  I(a) = {format_fraction(density_row_inner[a])}")
        print(f"  T(a) = {format_fraction(row_signed)}")
        print(f"  |T(a)| majorant = {format_fraction(row_abs)}")
        print(f"  row ratio = {row_ratio:.12g}")
        print()

        print("Residue-class summary")
        print("  residue        signed                  abs majorant            ratio        count   nonzero")
        summaries: list[tuple[int, Fraction, Fraction, float, int, int]] = []
        for r in range(modulus):
            bucket = [t for t in terms if t[0] % modulus == r]
            if not bucket:
                continue
            signed = sum((ca * term for _, _, _, term in bucket), Fraction(0, 1))
            majorant = sum((abs(ca * term) for _, _, _, term in bucket), Fraction(0, 1))
            ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
            nonzero = sum(1 for _, _, _, term in bucket if term != 0)
            summaries.append((r, signed, majorant, ratio, len(bucket), nonzero))
            print(
                f"  r={r:<3}"
                f"{float(signed):>18.6g}  "
                f"{float(majorant):>14.6g}  "
                f"{ratio:>10.6g}  "
                f"{len(bucket):>8}  "
                f"{nonzero:>7}"
            )
        print()

        print(f"Top residue classes by |signed| for a = {a} mod {modulus}")
        top_signed = sorted(summaries, key=lambda t: abs(t[1]), reverse=True)[:12]
        for r, signed, majorant, ratio, count, nonzero in top_signed:
            print(
                f"  r={r:<3} signed={float(signed):>14.6g}  "
                f"abs={float(majorant):>14.6g}  ratio={ratio:>10.6g}  "
                f"count={count:>5}  nonzero={nonzero:>5}"
            )
        print()

        print(f"Top residue classes by ratio for a = {a} mod {modulus}")
        top_ratio = sorted(
            [row for row in summaries if not math.isnan(row[3])],
            key=lambda t: t[3],
            reverse=True,
        )[:12]
        for r, signed, majorant, ratio, count, nonzero in top_ratio:
            print(
                f"  r={r:<3} ratio={ratio:>10.6g}  "
                f"signed={float(signed):>14.6g}  abs={float(majorant):>14.6g}  "
                f"count={count:>5}  nonzero={nonzero:>5}"
            )
        print()

        top_residues = [r for r, _, _, _, _, _ in top_signed[:8]]
        print(f"Detailed top b terms inside dominant classes for a = {a}")
        for r in top_residues:
            bucket = [t for t in terms if t[0] % modulus == r]
            signed = sum((ca * term for _, _, _, term in bucket), Fraction(0, 1))
            majorant = sum((abs(ca * term) for _, _, _, term in bucket), Fraction(0, 1))
            ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
            print(
                f"  class b ≡ {r} (mod {modulus}): count={len(bucket)}  "
                f"signed={float(signed):.6g}  abs={float(majorant):.6g}  ratio={ratio:.6g}"
            )
            print(
                "    b        fac(b)          c(b)                  "
                f"K_density({a},b)".ljust(28) +
                "c(a)c(b)K_density           period   blocks"
            )
            top_bucket = sorted(bucket, key=lambda t: abs(ca * t[3]), reverse=True)[:12]
            for b, cb, kd, term in top_bucket:
                period = centered_ramanujan_pair_block_period(a, b)
                blocks = H1 // period
                weighted = ca * term
                print(
                    f"    {b:<8}"
                    f"{format_factorization(b, spf):<16}"
                    f"{format_fraction(cb):>20}  "
                    f"{format_fraction(kd):>24}  "
                    f"{format_fraction(weighted):>24}  "
                    f"{period:>7}  {blocks:>6}"
                )
            print()
        return

    if args.fixed_a_bucket_scan is not None:
        a = args.fixed_a_bucket_scan
        if a not in density_row_terms:
            print("Fixed-a bucket scan")
            print(f"  a = {a}")
            print("  row not present on active odd surface")
            return

        if a == 7:
            modulus = 21
            neg_residues = {5, 11, 13, 12, 1}
            pos_residues = {15, 18, 6, 19, 20}
            residual_residues = set(range(modulus)) - neg_residues - pos_residues
        elif a == 5:
            modulus = 15
            neg_residues = {7, 9, 2, 4}
            pos_residues = {11, 13}
            residual_residues = set(range(modulus)) - neg_residues - pos_residues
        else:
            raise ValueError("fixed-a bucket scan is currently configured only for a=5 or a=7")

        terms = density_row_terms[a]
        ca = coeff_base(a, mu, phi)

        def bucket_data(name: str, residues: set[int]) -> tuple[str, Fraction, Fraction, float, int, int]:
            bucket = [t for t in terms if t[0] % modulus in residues]
            signed = sum((ca * term for _, _, _, term in bucket), Fraction(0, 1))
            majorant = sum((abs(ca * term) for _, _, _, term in bucket), Fraction(0, 1))
            ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
            count = len(bucket)
            nonzero = sum(1 for _, _, _, term in bucket if term != 0)
            return name, signed, majorant, ratio, count, nonzero

        neg = bucket_data("neg", neg_residues)
        pos = bucket_data("pos", pos_residues)
        residual = bucket_data("residual", residual_residues)
        main_signed = neg[1] + pos[1]
        main_majorant = neg[2] + pos[2]
        main_ratio = float(abs(main_signed) / main_majorant) if main_majorant != 0 else float("nan")

        print("Fixed-a bucket scan")
        print(f"  X = {X}")
        print(f"  a = {a}")
        print(f"  modulus = {modulus}")
        print(f"  fac(a) = {format_factorization(a, spf)}")
        print(f"  c(a) = {format_fraction(ca)}")
        print(f"  I(a) = {format_fraction(density_row_inner[a])}")
        print(f"  T(a) = {format_fraction(density_row_contrib[a])}")
        print()

        print("Bucket summary")
        print("  bucket           signed                  abs majorant            ratio        count   nonzero")
        for name, signed, majorant, ratio, count, nonzero in [neg, pos, residual]:
            print(
                f"  {name:<12}"
                f"{float(signed):>18.6g}  "
                f"{float(majorant):>14.6g}  "
                f"{ratio:>10.6g}  "
                f"{count:>8}  "
                f"{nonzero:>7}"
            )
        print()

        print("Coupled main buckets")
        print(f"  neg residues = {sorted(neg_residues)}")
        print(f"  pos residues = {sorted(pos_residues)}")
        print(f"  residual residues = {sorted(residual_residues)}")
        print(f"  T_main = T_neg + T_pos = {format_fraction(main_signed)}")
        print(f"  M_main = M_neg + M_pos = {format_fraction(main_majorant)}")
        print(f"  |T_main| / M_main = {main_ratio:.12g}")
        print()

        print("Per-residue breakdown inside buckets")
        print("  residue        signed                  abs majorant            ratio        count   nonzero   bucket")
        for r in range(modulus):
            bucket = [t for t in terms if t[0] % modulus == r]
            if not bucket:
                continue
            signed = sum((ca * term for _, _, _, term in bucket), Fraction(0, 1))
            majorant = sum((abs(ca * term) for _, _, _, term in bucket), Fraction(0, 1))
            ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
            nonzero = sum(1 for _, _, _, term in bucket if term != 0)
            label = "neg" if r in neg_residues else "pos" if r in pos_residues else "residual"
            print(
                f"  r={r:<3}"
                f"{float(signed):>18.6g}  "
                f"{float(majorant):>14.6g}  "
                f"{ratio:>10.6g}  "
                f"{len(bucket):>8}  "
                f"{nonzero:>7}   "
                f"{label}"
            )
        return

    if args.fixed_a_omega_scan is not None:
        a = args.fixed_a_omega_scan
        if a != 7:
            raise ValueError("fixed-a omega scan is currently configured only for a=7")

        scan_xs = args.scan_xs if args.scan_xs else [100000, 200000, 500000, 999998, 1000000, 1000002, 2000000, 5000000]
        main_residues = {5, 11, 13, 12, 1, 15, 18, 6, 19, 20}

        def omega_local(n: int) -> int:
            return len(factorization(n, spf))

        def build_density_row_for_x(x_local: int, a_local: int) -> list[tuple[int, Fraction, Fraction, Fraction]]:
            even_window_local = even_window_points(x_local)
            even_window_card_local = len(even_window_local)

            avg_counts_local: dict[int, dict[int, int]] = {}
            for q in set(odd_active_support + [1, 2]):
                counts = {g: 0 for g in divisors_cache[q]}
                for N in even_window_local:
                    counts[math.gcd(q, N)] += 1
                avg_counts_local[q] = counts

            def window_average_local(q: int, g: int) -> Fraction:
                return Fraction(avg_counts_local[q][g], even_window_card_local)

            def density_point_local(a1: int, b1: int, g: int, h: int) -> Fraction:
                block = centered_ramanujan_pair_block_period(a1, b1) // 2
                A = a1 // g
                B = b1 // h
                left_count = b1 * phi[A]
                right_count = a1 * phi[B]
                avg_a = window_average_local(a1, g)
                avg_b = window_average_local(b1, h)
                return Fraction(block, 1) * (
                    Fraction(left_count, block) - avg_a
                ) * (
                    Fraction(right_count, block) - avg_b
                )

            def row_summand_local(a1: int, b1: int) -> Fraction:
                if a1 == b1:
                    return Fraction(0, 1)
                if (H1 // centered_ramanujan_pair_block_period(a1, b1)) <= 0:
                    return Fraction(0, 1)
                s = Fraction(0, 1)
                for g in divisors_cache[a1]:
                    for h in divisors_cache[b1]:
                        coeff = gcd_class_coeff(a1, g, mu, phi) * gcd_class_coeff(b1, h, mu, phi)
                        s += Fraction(coeff, 1) * density_point_local(a1, b1, g, h)
                return s

            out: list[tuple[int, Fraction, Fraction, Fraction]] = []
            for b in odd_active_support:
                if math.gcd(a_local, b) != 1:
                    continue
                if b % 21 not in main_residues:
                    continue
                cb = coeff_base(b, mu, phi)
                kd = row_summand_local(a_local, b)
                weighted = coeff_base(a_local, mu, phi) * cb * kd
                out.append((b, cb, kd, weighted))
            return out

        rows_by_x: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {
            x_local: build_density_row_for_x(x_local, a) for x_local in scan_xs
        }

        print("Fixed-a omega scan")
        print(f"  a = {a}")
        print(f"  main residues mod 21 = {sorted(main_residues)}")
        print(f"  scan X values = {scan_xs}")
        print()

        print("Per-window omega-bucket summary")
        print("  X         bucket     signed           abs majorant      ratio        abs-mass share")
        for x_local in scan_xs:
            rows = rows_by_x[x_local]
            main_abs = sum((abs(weighted) for _, _, _, weighted in rows), Fraction(0, 1))
            for label, pred in [
                ("omega=1", lambda b: omega_local(b) == 1),
                ("omega=2", lambda b: omega_local(b) == 2),
                ("omega>=3", lambda b: omega_local(b) >= 3),
            ]:
                bucket = [row for row in rows if pred(row[0])]
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
                share = float(majorant / main_abs) if main_abs != 0 else float("nan")
                print(
                    f"  {x_local:<8}"
                    f"{label:<10}"
                    f"{float(signed):>14.6g}  "
                    f"{float(majorant):>14.6g}  "
                    f"{ratio:>10.6g}  "
                    f"{share:>14.6g}"
                )
            print()

        print("Bucket ranges over scan")
        for label, pred in [
            ("omega=1", lambda b: omega_local(b) == 1),
            ("omega=2", lambda b: omega_local(b) == 2),
            ("omega>=3", lambda b: omega_local(b) >= 3),
        ]:
            ratios: list[float] = []
            shares: list[float] = []
            for x_local in scan_xs:
                rows = rows_by_x[x_local]
                main_abs = sum((abs(weighted) for _, _, _, weighted in rows), Fraction(0, 1))
                bucket = [row for row in rows if pred(row[0])]
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                if majorant != 0:
                    ratios.append(float(abs(signed) / majorant))
                if main_abs != 0:
                    shares.append(float(majorant / main_abs))
            print(
                f"  {label:<10}"
                f"ratio range=[{min(ratios):.6g}, {max(ratios):.6g}]  avg={sum(ratios)/len(ratios):.6g}   "
                f"abs-share range=[{min(shares):.6g}, {max(shares):.6g}]  avg={sum(shares)/len(shares):.6g}"
            )
        return

    if args.fixed_a_omega2_three_scan is not None:
        a = args.fixed_a_omega2_three_scan
        if a != 7:
            raise ValueError("fixed-a omega2 three scan is currently configured only for a=7")

        scan_xs = args.scan_xs if args.scan_xs else [100000, 200000, 500000, 999998, 1000000, 1000002, 2000000, 5000000]
        main_residues = {5, 11, 13, 12, 1, 15, 18, 6, 19, 20}

        def omega_local(n: int) -> int:
            return len(factorization(n, spf))

        def build_density_row_for_x(x_local: int, a_local: int) -> list[tuple[int, Fraction, Fraction, Fraction]]:
            even_window_local = even_window_points(x_local)
            even_window_card_local = len(even_window_local)

            avg_counts_local: dict[int, dict[int, int]] = {}
            for q in set(odd_active_support + [1, 2]):
                counts = {g: 0 for g in divisors_cache[q]}
                for N in even_window_local:
                    counts[math.gcd(q, N)] += 1
                avg_counts_local[q] = counts

            def window_average_local(q: int, g: int) -> Fraction:
                return Fraction(avg_counts_local[q][g], even_window_card_local)

            def density_point_local(a1: int, b1: int, g: int, h: int) -> Fraction:
                block = centered_ramanujan_pair_block_period(a1, b1) // 2
                A = a1 // g
                B = b1 // h
                left_count = b1 * phi[A]
                right_count = a1 * phi[B]
                avg_a = window_average_local(a1, g)
                avg_b = window_average_local(b1, h)
                return Fraction(block, 1) * (
                    Fraction(left_count, block) - avg_a
                ) * (
                    Fraction(right_count, block) - avg_b
                )

            def row_summand_local(a1: int, b1: int) -> Fraction:
                if a1 == b1:
                    return Fraction(0, 1)
                if (H1 // centered_ramanujan_pair_block_period(a1, b1)) <= 0:
                    return Fraction(0, 1)
                s = Fraction(0, 1)
                for g in divisors_cache[a1]:
                    for h in divisors_cache[b1]:
                        coeff = gcd_class_coeff(a1, g, mu, phi) * gcd_class_coeff(b1, h, mu, phi)
                        s += Fraction(coeff, 1) * density_point_local(a1, b1, g, h)
                return s

            out: list[tuple[int, Fraction, Fraction, Fraction]] = []
            for b in odd_active_support:
                if math.gcd(a_local, b) != 1:
                    continue
                if b % 21 not in main_residues:
                    continue
                cb = coeff_base(b, mu, phi)
                kd = row_summand_local(a_local, b)
                weighted = coeff_base(a_local, mu, phi) * cb * kd
                out.append((b, cb, kd, weighted))
            return out

        rows_by_x: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {
            x_local: build_density_row_for_x(x_local, a) for x_local in scan_xs
        }

        print("Fixed-a omega=2 three-divisibility scan")
        print(f"  a = {a}")
        print(f"  scan X values = {scan_xs}")
        print()

        print("Per-window omega=2 split")
        print("  X         bucket            signed           abs majorant      ratio        abs-mass share")
        for x_local in scan_xs:
            rows = rows_by_x[x_local]
            omega2_rows = [row for row in rows if omega_local(row[0]) == 2]
            omega2_abs = sum((abs(weighted) for _, _, _, weighted in omega2_rows), Fraction(0, 1))
            for label, pred in [
                ("omega2,3|b", lambda b: omega_local(b) == 2 and b % 3 == 0),
                ("omega2,3∤b", lambda b: omega_local(b) == 2 and b % 3 != 0),
            ]:
                bucket = [row for row in rows if pred(row[0])]
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
                share = float(majorant / omega2_abs) if omega2_abs != 0 else float("nan")
                print(
                    f"  {x_local:<8}"
                    f"{label:<14}"
                    f"{float(signed):>14.6g}  "
                    f"{float(majorant):>14.6g}  "
                    f"{ratio:>10.6g}  "
                    f"{share:>14.6g}"
                )
            print()

        print("Bucket ranges over scan")
        for label, pred in [
            ("omega2,3|b", lambda b: omega_local(b) == 2 and b % 3 == 0),
            ("omega2,3∤b", lambda b: omega_local(b) == 2 and b % 3 != 0),
        ]:
            ratios: list[float] = []
            shares: list[float] = []
            for x_local in scan_xs:
                rows = rows_by_x[x_local]
                omega2_rows = [row for row in rows if omega_local(row[0]) == 2]
                omega2_abs = sum((abs(weighted) for _, _, _, weighted in omega2_rows), Fraction(0, 1))
                bucket = [row for row in rows if pred(row[0])]
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                if majorant != 0:
                    ratios.append(float(abs(signed) / majorant))
                if omega2_abs != 0:
                    shares.append(float(majorant / omega2_abs))
            print(
                f"  {label:<14}"
                f"ratio range=[{min(ratios):.6g}, {max(ratios):.6g}]  avg={sum(ratios)/len(ratios):.6g}   "
                f"abs-share range=[{min(shares):.6g}, {max(shares):.6g}]  avg={sum(shares)/len(shares):.6g}"
            )
        return

    if args.fixed_a_omega2_three_five_scan is not None:
        a = args.fixed_a_omega2_three_five_scan
        if a != 7:
            raise ValueError("fixed-a omega2 three-five scan is currently configured only for a=7")

        scan_xs = args.scan_xs if args.scan_xs else [100000, 200000, 500000, 999998, 1000000, 1000002, 2000000, 5000000]
        main_residues = {5, 11, 13, 12, 1, 15, 18, 6, 19, 20}

        def omega_local(n: int) -> int:
            return len(factorization(n, spf))

        def build_density_row_for_x(x_local: int, a_local: int) -> list[tuple[int, Fraction, Fraction, Fraction]]:
            even_window_local = even_window_points(x_local)
            even_window_card_local = len(even_window_local)

            avg_counts_local: dict[int, dict[int, int]] = {}
            for q in set(odd_active_support + [1, 2]):
                counts = {g: 0 for g in divisors_cache[q]}
                for N in even_window_local:
                    counts[math.gcd(q, N)] += 1
                avg_counts_local[q] = counts

            def window_average_local(q: int, g: int) -> Fraction:
                return Fraction(avg_counts_local[q][g], even_window_card_local)

            def density_point_local(a1: int, b1: int, g: int, h: int) -> Fraction:
                block = centered_ramanujan_pair_block_period(a1, b1) // 2
                A = a1 // g
                B = b1 // h
                left_count = b1 * phi[A]
                right_count = a1 * phi[B]
                avg_a = window_average_local(a1, g)
                avg_b = window_average_local(b1, h)
                return Fraction(block, 1) * (
                    Fraction(left_count, block) - avg_a
                ) * (
                    Fraction(right_count, block) - avg_b
                )

            def row_summand_local(a1: int, b1: int) -> Fraction:
                if a1 == b1:
                    return Fraction(0, 1)
                if (H1 // centered_ramanujan_pair_block_period(a1, b1)) <= 0:
                    return Fraction(0, 1)
                s = Fraction(0, 1)
                for g in divisors_cache[a1]:
                    for h in divisors_cache[b1]:
                        coeff = gcd_class_coeff(a1, g, mu, phi) * gcd_class_coeff(b1, h, mu, phi)
                        s += Fraction(coeff, 1) * density_point_local(a1, b1, g, h)
                return s

            out: list[tuple[int, Fraction, Fraction, Fraction]] = []
            for b in odd_active_support:
                if math.gcd(a_local, b) != 1:
                    continue
                if b % 21 not in main_residues:
                    continue
                cb = coeff_base(b, mu, phi)
                kd = row_summand_local(a_local, b)
                weighted = coeff_base(a_local, mu, phi) * cb * kd
                out.append((b, cb, kd, weighted))
            return out

        rows_by_x: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {
            x_local: build_density_row_for_x(x_local, a) for x_local in scan_xs
        }

        def is_omega2_three_dvd(b: int) -> bool:
            return omega_local(b) == 2 and b % 3 == 0

        def is_omega2_three_five_dvd(b: int) -> bool:
            return omega_local(b) == 2 and b % 3 == 0 and b % 5 == 0

        def is_omega2_three_five_not_dvd(b: int) -> bool:
            return omega_local(b) == 2 and b % 3 == 0 and b % 5 != 0

        print("Fixed-a omega=2, 3|b, 5-split scan")
        print(f"  a = {a}")
        print(f"  scan X values = {scan_xs}")
        print()

        print("Per-window split inside omega=2, 3|b")
        print("  X         bucket              signed           abs majorant      ratio        abs-share within 3|b")
        for x_local in scan_xs:
            rows = rows_by_x[x_local]
            three_rows = [row for row in rows if is_omega2_three_dvd(row[0])]
            three_abs = sum((abs(weighted) for _, _, _, weighted in three_rows), Fraction(0, 1))
            for label, pred in [
                ("omega2,3|b,5|b", is_omega2_three_five_dvd),
                ("omega2,3|b,5∤b", is_omega2_three_five_not_dvd),
            ]:
                bucket = [row for row in rows if pred(row[0])]
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
                share = float(majorant / three_abs) if three_abs != 0 else float("nan")
                print(
                    f"  {x_local:<8}"
                    f"{label:<16}"
                    f"{float(signed):>14.6g}  "
                    f"{float(majorant):>14.6g}  "
                    f"{ratio:>10.6g}  "
                    f"{share:>18.6g}"
                )
            print()

        print("Bucket ranges over scan")
        for label, pred in [
            ("omega2,3|b,5|b", is_omega2_three_five_dvd),
            ("omega2,3|b,5∤b", is_omega2_three_five_not_dvd),
        ]:
            ratios: list[float] = []
            shares: list[float] = []
            for x_local in scan_xs:
                rows = rows_by_x[x_local]
                three_rows = [row for row in rows if is_omega2_three_dvd(row[0])]
                three_abs = sum((abs(weighted) for _, _, _, weighted in three_rows), Fraction(0, 1))
                bucket = [row for row in rows if pred(row[0])]
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                if majorant != 0:
                    ratios.append(float(abs(signed) / majorant))
                if three_abs != 0:
                    shares.append(float(majorant / three_abs))
            print(
                f"  {label:<16}"
                f"ratio range=[{min(ratios):.6g}, {max(ratios):.6g}]  avg={sum(ratios)/len(ratios):.6g}   "
                f"share range=[{min(shares):.6g}, {max(shares):.6g}]  avg={sum(shares)/len(shares):.6g}"
            )
        print()

        print("Top second-prime families inside omega=2, 3|b, 5∤b")
        print("  X         p      signed           abs majorant      ratio        count")
        for x_local in scan_xs:
            rows = rows_by_x[x_local]
            five_not_rows = [row for row in rows if is_omega2_three_five_not_dvd(row[0])]
            family: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {}
            for row in five_not_rows:
                b = row[0]
                p = b // 3
                family.setdefault(p, []).append(row)
            ranked = []
            for p, bucket in family.items():
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
                ranked.append((majorant, p, signed, ratio, len(bucket)))
            ranked.sort(reverse=True)
            for majorant, p, signed, ratio, count in ranked[:8]:
                print(
                    f"  {x_local:<8}"
                    f"{p:<6}"
                    f"{float(signed):>14.6g}  "
                    f"{float(majorant):>14.6g}  "
                    f"{ratio:>10.6g}  "
                    f"{count:>8}"
                )
            print()
        return

    if args.fixed_a_omega2_three_five_not_p_scan is not None:
        a = args.fixed_a_omega2_three_five_not_p_scan
        if a != 7:
            raise ValueError("fixed-a omega2 three-five-not-p scan is currently configured only for a=7")

        scan_xs = args.scan_xs if args.scan_xs else [100000, 200000, 500000, 999998, 1000000, 1000002, 2000000, 5000000]
        main_residues = {5, 11, 13, 12, 1, 15, 18, 6, 19, 20}

        def omega_local(n: int) -> int:
            return len(factorization(n, spf))

        def build_density_row_for_x(x_local: int, a_local: int) -> list[tuple[int, Fraction, Fraction, Fraction]]:
            even_window_local = even_window_points(x_local)
            even_window_card_local = len(even_window_local)

            avg_counts_local: dict[int, dict[int, int]] = {}
            for q in set(odd_active_support + [1, 2]):
                counts = {g: 0 for g in divisors_cache[q]}
                for N in even_window_local:
                    counts[math.gcd(q, N)] += 1
                avg_counts_local[q] = counts

            def window_average_local(q: int, g: int) -> Fraction:
                return Fraction(avg_counts_local[q][g], even_window_card_local)

            def density_point_local(a1: int, b1: int, g: int, h: int) -> Fraction:
                block = centered_ramanujan_pair_block_period(a1, b1) // 2
                A = a1 // g
                B = b1 // h
                left_count = b1 * phi[A]
                right_count = a1 * phi[B]
                avg_a = window_average_local(a1, g)
                avg_b = window_average_local(b1, h)
                return Fraction(block, 1) * (
                    Fraction(left_count, block) - avg_a
                ) * (
                    Fraction(right_count, block) - avg_b
                )

            def row_summand_local(a1: int, b1: int) -> Fraction:
                if a1 == b1:
                    return Fraction(0, 1)
                if (H1 // centered_ramanujan_pair_block_period(a1, b1)) <= 0:
                    return Fraction(0, 1)
                s = Fraction(0, 1)
                for g in divisors_cache[a1]:
                    for h in divisors_cache[b1]:
                        coeff = gcd_class_coeff(a1, g, mu, phi) * gcd_class_coeff(b1, h, mu, phi)
                        s += Fraction(coeff, 1) * density_point_local(a1, b1, g, h)
                return s

            out: list[tuple[int, Fraction, Fraction, Fraction]] = []
            for b in odd_active_support:
                if math.gcd(a_local, b) != 1:
                    continue
                if b % 21 not in main_residues:
                    continue
                cb = coeff_base(b, mu, phi)
                kd = row_summand_local(a_local, b)
                weighted = coeff_base(a_local, mu, phi) * cb * kd
                out.append((b, cb, kd, weighted))
            return out

        def is_live_family(b: int) -> bool:
            return omega_local(b) == 2 and b % 3 == 0 and b % 5 != 0

        rows_by_x: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {
            x_local: build_density_row_for_x(x_local, a) for x_local in scan_xs
        }

        print("Fixed-a omega=2, 3|b, 5∤b live-family second-prime scan")
        print(f"  a = {a}")
        print(f"  scan X values = {scan_xs}")
        print()

        for modulus in [7, 5, 35]:
            print(f"Grouping by p mod {modulus}, where b = 3p")
            print("  X         residue  signed           abs majorant      ratio        abs-share within live family")
            for x_local in scan_xs:
                rows = rows_by_x[x_local]
                live_rows = [row for row in rows if is_live_family(row[0])]
                live_abs = sum((abs(weighted) for _, _, _, weighted in live_rows), Fraction(0, 1))
                residue_rows: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {}
                for row in live_rows:
                    b = row[0]
                    p = b // 3
                    residue_rows.setdefault(p % modulus, []).append(row)
                ranked = []
                for r, bucket in residue_rows.items():
                    signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                    majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                    ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
                    share = float(majorant / live_abs) if live_abs != 0 else float("nan")
                    ranked.append((majorant, r, signed, ratio, share, len(bucket)))
                ranked.sort(reverse=True)
                for majorant, r, signed, ratio, share, count in ranked[:8]:
                    print(
                        f"  {x_local:<8}"
                        f"{r:<8}"
                        f"{float(signed):>14.6g}  "
                        f"{float(majorant):>14.6g}  "
                        f"{ratio:>10.6g}  "
                        f"{share:>18.6g}  "
                        f"{count:>8}"
                    )
                print()

            print(f"Residue-class ranges mod {modulus}")
            residue_stats: dict[int, tuple[list[float], list[float]]] = {}
            for x_local in scan_xs:
                rows = rows_by_x[x_local]
                live_rows = [row for row in rows if is_live_family(row[0])]
                live_abs = sum((abs(weighted) for _, _, _, weighted in live_rows), Fraction(0, 1))
                residue_rows: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {}
                for row in live_rows:
                    p = row[0] // 3
                    residue_rows.setdefault(p % modulus, []).append(row)
                for r, bucket in residue_rows.items():
                    signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                    majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                    if r not in residue_stats:
                        residue_stats[r] = ([], [])
                    if majorant != 0:
                        residue_stats[r][0].append(float(abs(signed) / majorant))
                    if live_abs != 0:
                        residue_stats[r][1].append(float(majorant / live_abs))
            ranked_stats = []
            for r, (ratios, shares) in residue_stats.items():
                ranked_stats.append((sum(shares) / len(shares), r, ratios, shares))
            ranked_stats.sort(reverse=True)
            for _avg_share, r, ratios, shares in ranked_stats[:10]:
                print(
                    f"  residue {r:<4}"
                    f"ratio range=[{min(ratios):.6g}, {max(ratios):.6g}]  avg={sum(ratios)/len(ratios):.6g}   "
                    f"share range=[{min(shares):.6g}, {max(shares):.6g}]  avg={sum(shares)/len(shares):.6g}"
                )
            print()
        return

    if args.fixed_a_omega2_notthree_family_scan is not None:
        a = args.fixed_a_omega2_notthree_family_scan
        if a != 7:
            raise ValueError("fixed-a omega2 not-three family scan is currently configured only for a=7")

        scan_xs = args.scan_xs if args.scan_xs else [100000, 200000, 500000, 999998, 1000000, 1000002, 2000000, 5000000]
        main_residues = {5, 11, 13, 12, 1, 15, 18, 6, 19, 20}

        def omega_local(n: int) -> int:
            return len(factorization(n, spf))

        def smallest_prime_factor_local(n: int) -> int:
            fac = factorization(n, spf)
            return min(fac)

        def build_density_row_for_x(x_local: int, a_local: int) -> list[tuple[int, Fraction, Fraction, Fraction]]:
            even_window_local = even_window_points(x_local)
            even_window_card_local = len(even_window_local)

            avg_counts_local: dict[int, dict[int, int]] = {}
            for q in set(odd_active_support + [1, 2]):
                counts = {g: 0 for g in divisors_cache[q]}
                for N in even_window_local:
                    counts[math.gcd(q, N)] += 1
                avg_counts_local[q] = counts

            def window_average_local(q: int, g: int) -> Fraction:
                return Fraction(avg_counts_local[q][g], even_window_card_local)

            def density_point_local(a1: int, b1: int, g: int, h: int) -> Fraction:
                block = centered_ramanujan_pair_block_period(a1, b1) // 2
                A = a1 // g
                B = b1 // h
                left_count = b1 * phi[A]
                right_count = a1 * phi[B]
                avg_a = window_average_local(a1, g)
                avg_b = window_average_local(b1, h)
                return Fraction(block, 1) * (
                    Fraction(left_count, block) - avg_a
                ) * (
                    Fraction(right_count, block) - avg_b
                )

            def row_summand_local(a1: int, b1: int) -> Fraction:
                if a1 == b1:
                    return Fraction(0, 1)
                if (H1 // centered_ramanujan_pair_block_period(a1, b1)) <= 0:
                    return Fraction(0, 1)
                s = Fraction(0, 1)
                for g in divisors_cache[a1]:
                    for h in divisors_cache[b1]:
                        coeff = gcd_class_coeff(a1, g, mu, phi) * gcd_class_coeff(b1, h, mu, phi)
                        s += Fraction(coeff, 1) * density_point_local(a1, b1, g, h)
                return s

            out: list[tuple[int, Fraction, Fraction, Fraction]] = []
            for b in odd_active_support:
                if math.gcd(a_local, b) != 1:
                    continue
                if b % 21 not in main_residues:
                    continue
                cb = coeff_base(b, mu, phi)
                kd = row_summand_local(a_local, b)
                weighted = coeff_base(a_local, mu, phi) * cb * kd
                out.append((b, cb, kd, weighted))
            return out

        def is_omega2_notthree(b: int) -> bool:
            return omega_local(b) == 2 and b % 3 != 0

        rows_by_x: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {
            x_local: build_density_row_for_x(x_local, a) for x_local in scan_xs
        }

        print("Fixed-a omega=2, 3∤b family scan")
        print(f"  a = {a}")
        print(f"  scan X values = {scan_xs}")
        print()

        print("Per-window split inside omega=2, 3∤b")
        print("  X         bucket            signed           abs majorant      ratio        abs-share within 3∤b")
        for x_local in scan_xs:
            rows = rows_by_x[x_local]
            notthree_rows = [row for row in rows if is_omega2_notthree(row[0])]
            notthree_abs = sum((abs(weighted) for _, _, _, weighted in notthree_rows), Fraction(0, 1))
            for label, pred in [
                ("omega2,3∤b,5|b", lambda b: is_omega2_notthree(b) and b % 5 == 0),
                ("omega2,3∤b,5∤b", lambda b: is_omega2_notthree(b) and b % 5 != 0),
            ]:
                bucket = [row for row in rows if pred(row[0])]
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
                share = float(majorant / notthree_abs) if notthree_abs != 0 else float("nan")
                print(
                    f"  {x_local:<8}"
                    f"{label:<16}"
                    f"{float(signed):>14.6g}  "
                    f"{float(majorant):>14.6g}  "
                    f"{ratio:>10.6g}  "
                    f"{share:>18.6g}"
                )
            print()

        print("Bucket ranges over scan")
        for label, pred in [
            ("omega2,3∤b,5|b", lambda b: is_omega2_notthree(b) and b % 5 == 0),
            ("omega2,3∤b,5∤b", lambda b: is_omega2_notthree(b) and b % 5 != 0),
        ]:
            ratios: list[float] = []
            shares: list[float] = []
            for x_local in scan_xs:
                rows = rows_by_x[x_local]
                notthree_rows = [row for row in rows if is_omega2_notthree(row[0])]
                notthree_abs = sum((abs(weighted) for _, _, _, weighted in notthree_rows), Fraction(0, 1))
                bucket = [row for row in rows if pred(row[0])]
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                if majorant != 0:
                    ratios.append(float(abs(signed) / majorant))
                if notthree_abs != 0:
                    shares.append(float(majorant / notthree_abs))
            print(
                f"  {label:<16}"
                f"ratio range=[{min(ratios):.6g}, {max(ratios):.6g}]  avg={sum(ratios)/len(ratios):.6g}   "
                f"share range=[{min(shares):.6g}, {max(shares):.6g}]  avg={sum(shares)/len(shares):.6g}"
            )
        print()

        print("Smallest-prime-factor groups inside omega=2, 3∤b")
        print("  X         spf    signed           abs majorant      ratio        abs-share within 3∤b")
        for x_local in scan_xs:
            rows = rows_by_x[x_local]
            notthree_rows = [row for row in rows if is_omega2_notthree(row[0])]
            notthree_abs = sum((abs(weighted) for _, _, _, weighted in notthree_rows), Fraction(0, 1))
            spf_groups: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {}
            for row in notthree_rows:
                spf_groups.setdefault(smallest_prime_factor_local(row[0]), []).append(row)
            ranked = []
            for p, bucket in spf_groups.items():
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                ratio = float(abs(signed) / majorant) if majorant != 0 else float("nan")
                share = float(majorant / notthree_abs) if notthree_abs != 0 else float("nan")
                ranked.append((majorant, p, signed, ratio, share, len(bucket)))
            ranked.sort(reverse=True)
            for majorant, p, signed, ratio, share, count in ranked[:8]:
                print(
                    f"  {x_local:<8}"
                    f"{p:<6}"
                    f"{float(signed):>14.6g}  "
                    f"{float(majorant):>14.6g}  "
                    f"{ratio:>10.6g}  "
                    f"{share:>18.6g}  "
                    f"{count:>8}"
                )
            print()

        print("Smallest-prime-factor ranges over scan")
        spf_stats: dict[int, tuple[list[float], list[float]]] = {}
        for x_local in scan_xs:
            rows = rows_by_x[x_local]
            notthree_rows = [row for row in rows if is_omega2_notthree(row[0])]
            notthree_abs = sum((abs(weighted) for _, _, _, weighted in notthree_rows), Fraction(0, 1))
            spf_groups: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {}
            for row in notthree_rows:
                spf_groups.setdefault(smallest_prime_factor_local(row[0]), []).append(row)
            for p, bucket in spf_groups.items():
                signed = sum((weighted for _, _, _, weighted in bucket), Fraction(0, 1))
                majorant = sum((abs(weighted) for _, _, _, weighted in bucket), Fraction(0, 1))
                if p not in spf_stats:
                    spf_stats[p] = ([], [])
                if majorant != 0:
                    spf_stats[p][0].append(float(abs(signed) / majorant))
                if notthree_abs != 0:
                    spf_stats[p][1].append(float(majorant / notthree_abs))
        ranked_stats = []
        for p, (ratios, shares) in spf_stats.items():
            ranked_stats.append((sum(shares) / len(shares), p, ratios, shares))
        ranked_stats.sort(reverse=True)
        for _avg_share, p, ratios, shares in ranked_stats[:10]:
            if not ratios or not shares:
                continue
            print(
                f"  spf {p:<4}"
                f"ratio range=[{min(ratios):.6g}, {max(ratios):.6g}]  avg={sum(ratios)/len(ratios):.6g}   "
                f"share range=[{min(shares):.6g}, {max(shares):.6g}]  avg={sum(shares)/len(shares):.6g}"
            )
        return

    if args.fixed_a_dominant_scan is not None:
        a = args.fixed_a_dominant_scan
        if a != 7:
            raise ValueError("fixed-a dominant scan is currently configured only for a=7")

        scan_xs = args.scan_xs if args.scan_xs else [100000, 200000, 500000, 999998, 1000000, 1000002, 2000000, 5000000]
        dominant_bs = [15, 95, 123, 165, 167, 195, 285, 393, 435, 501, 503, 505, 543, 645, 663, 685, 687]
        main_residues = {5, 11, 13, 12, 1, 15, 18, 6, 19, 20}

        def build_density_row_for_x(x_local: int, a_local: int) -> list[tuple[int, Fraction, Fraction, Fraction]]:
            even_window_local = even_window_points(x_local)
            even_window_card_local = len(even_window_local)

            avg_counts_local: dict[int, dict[int, int]] = {}
            for q in set(odd_active_support + [1, 2]):
                counts = {g: 0 for g in divisors_cache[q]}
                for N in even_window_local:
                    counts[math.gcd(q, N)] += 1
                avg_counts_local[q] = counts

            def window_average_local(q: int, g: int) -> Fraction:
                return Fraction(avg_counts_local[q][g], even_window_card_local)

            def density_point_local(a1: int, b1: int, g: int, h: int) -> Fraction:
                block = centered_ramanujan_pair_block_period(a1, b1) // 2
                A = a1 // g
                B = b1 // h
                left_count = b1 * phi[A]
                right_count = a1 * phi[B]
                avg_a = window_average_local(a1, g)
                avg_b = window_average_local(b1, h)
                return Fraction(block, 1) * (
                    Fraction(left_count, block) - avg_a
                ) * (
                    Fraction(right_count, block) - avg_b
                )

            def row_summand_local(a1: int, b1: int) -> Fraction:
                if a1 == b1:
                    return Fraction(0, 1)
                if (H1 // centered_ramanujan_pair_block_period(a1, b1)) <= 0:
                    return Fraction(0, 1)
                s = Fraction(0, 1)
                for g in divisors_cache[a1]:
                    for h in divisors_cache[b1]:
                        coeff = gcd_class_coeff(a1, g, mu, phi) * gcd_class_coeff(b1, h, mu, phi)
                        s += Fraction(coeff, 1) * density_point_local(a1, b1, g, h)
                return s

            out: list[tuple[int, Fraction, Fraction, Fraction]] = []
            for b in odd_active_support:
                if math.gcd(a_local, b) != 1:
                    continue
                if b % 21 not in main_residues:
                    continue
                cb = coeff_base(b, mu, phi)
                kd = row_summand_local(a_local, b)
                weighted = coeff_base(a_local, mu, phi) * cb * kd
                out.append((b, cb, kd, weighted))
            return out

        rows_by_x: dict[int, list[tuple[int, Fraction, Fraction, Fraction]]] = {
            x_local: build_density_row_for_x(x_local, a) for x_local in scan_xs
        }

        print("Fixed-a dominant-set scan")
        print(f"  a = {a}")
        print(f"  dominant set D = {dominant_bs}")
        print(f"  scan X values = {scan_xs}")
        print()

        print("Per-window main-vs-dominant capture")
        print("  X         T_main           |T_main| abs       T_dom            |T_dom| abs        abs capture   signed capture")
        for x_local in scan_xs:
            rows = rows_by_x[x_local]
            main_signed = sum((weighted for _, _, _, weighted in rows), Fraction(0, 1))
            main_abs = sum((abs(weighted) for _, _, _, weighted in rows), Fraction(0, 1))
            dom_rows = [row for row in rows if row[0] in dominant_bs]
            dom_signed = sum((weighted for _, _, _, weighted in dom_rows), Fraction(0, 1))
            dom_abs = sum((abs(weighted) for _, _, _, weighted in dom_rows), Fraction(0, 1))
            abs_capture = float(dom_abs / main_abs) if main_abs != 0 else float("nan")
            signed_capture = float(dom_signed / main_signed) if main_signed != 0 else float("nan")
            print(
                f"  {x_local:<8}"
                f"{float(main_signed):>14.6g}  "
                f"{float(main_abs):>14.6g}  "
                f"{float(dom_signed):>14.6g}  "
                f"{float(dom_abs):>14.6g}  "
                f"{abs_capture:>12.6g}  "
                f"{signed_capture:>13.6g}"
            )
        print()

        print("Per-b stability table")
        print("  b    fac            top10 count   max|contrib|      sign pattern        Xmod/(14b) by X")
        for b in dominant_bs:
            fac = format_factorization(b, spf)
            top10_count = 0
            max_abs = Fraction(0, 1)
            signs: list[str] = []
            aligns: list[str] = []
            for x_local in scan_xs:
                rows = rows_by_x[x_local]
                top10_bs = {row[0] for row in sorted(rows, key=lambda t: abs(t[3]), reverse=True)[:10]}
                if b in top10_bs:
                    top10_count += 1
                row = next((row for row in rows if row[0] == b), None)
                if row is None:
                    signs.append(".")
                    aligns.append(".")
                    continue
                weighted = row[3]
                max_abs = max(max_abs, abs(weighted))
                if weighted > 0:
                    signs.append("+")
                elif weighted < 0:
                    signs.append("-")
                else:
                    signs.append("0")
                period = centered_ramanujan_pair_block_period(a, b)
                aligns.append(f"{x_local % period}/{period}")
            print(
                f"  {b:<4} {fac:<14} {top10_count:^11} "
                f"{float(max_abs):>14.6g}      "
                f"{''.join(signs):<14} "
                f"{', '.join(aligns)}"
            )
        print()

        print("Tail summary")
        print("  X         T_tail           |T_tail| abs       abs tail ratio")
        for x_local in scan_xs:
            rows = rows_by_x[x_local]
            tail_rows = [row for row in rows if row[0] not in dominant_bs]
            tail_signed = sum((weighted for _, _, _, weighted in tail_rows), Fraction(0, 1))
            tail_abs = sum((abs(weighted) for _, _, _, weighted in tail_rows), Fraction(0, 1))
            main_abs = sum((abs(weighted) for _, _, _, weighted in rows), Fraction(0, 1))
            tail_ratio = float(tail_abs / main_abs) if main_abs != 0 else float("nan")
            print(
                f"  {x_local:<8}"
                f"{float(tail_signed):>14.6g}  "
                f"{float(tail_abs):>14.6g}  "
                f"{tail_ratio:>14.6g}"
            )
        return

    endpoint_two_one = coeff_base(2, mu, phi) * coeff_base(1, mu, phi) * periodic_main_generic(2, 1)
    endpoint_one_two = coeff_base(1, mu, phi) * coeff_base(2, mu, phi) * periodic_main_generic(1, 2)
    coprime_bound_rhs = abs(endpoint_one_two) + abs(endpoint_two_one) + abs(unified_exact) + combined_one_block_majorant

    sym_diff_abs: dict[str, Fraction] = {k: Fraction(0, 1) for k in piece_names}
    antisym_diff_abs: dict[str, Fraction] = {k: Fraction(0, 1) for k in piece_names}
    max_sym_diff: dict[str, Fraction] = {k: Fraction(0, 1) for k in piece_names}
    max_antisym_diff: dict[str, Fraction] = {k: Fraction(0, 1) for k in piece_names}
    for i, a in enumerate(odd_active_support):
        for b in odd_active_support[i + 1:]:
            if a == b or math.gcd(a, b) != 1:
                continue
            if a * b > H1 // 2:
                continue
            for piece in piece_names:
                sab = piece_pair_values[(piece, a, b)]
                sba = piece_pair_values[(piece, b, a)]
                symd = sab - sba
                antisymd = sab + sba
                sym_diff_abs[piece] += abs(symd)
                antisym_diff_abs[piece] += abs(antisymd)
                max_sym_diff[piece] = max(max_sym_diff[piece], abs(symd))
                max_antisym_diff[piece] = max(max_antisym_diff[piece], abs(antisymd))

    print("Unified odd-surface coprime audit")
    print(f"  X = {X}")
    print(f"  Q0 = {q0}")
    print(f"  H+1 = {H1}")
    print(f"  even window card = {even_window_card}")
    print(f"  active odd support size = {len(odd_active_support)}")
    print(f"  active ordered coprime off-diagonal odd pairs = {active_pair_count}")
    print(f"  multiplicities seen on active support = {sorted(multiplicities_seen)}")
    print()

    print("Scalar-free exact values")
    print(f"  unified exact sum = {format_fraction(unified_exact)}")
    print(f"  unified exact sum (float) = {float(unified_exact):.12g}")
    print(f"  unified abs sum with exact effective weight = {format_fraction(unified_abs_exact_weight)}")
    print(f"  unified abs sum with exact effective weight (float) = {float(unified_abs_exact_weight):.12g}")
    print(f"  crude 3*|c(a)c(b)|*|K(a,b)| majorant = {format_fraction(unified_abs_crude_three)}")
    print(f"  crude 3*|c(a)c(b)|*|K(a,b)| majorant (float) = {float(unified_abs_crude_three):.12g}")
    print(f"  endpoint (1,2) = {format_fraction(endpoint_one_two)}")
    print(f"  endpoint (1,2) (float) = {float(endpoint_one_two):.12g}")
    print(f"  endpoint (2,1) = {format_fraction(endpoint_two_one)}")
    print(f"  endpoint (2,1) (float) = {float(endpoint_two_one):.12g}")
    print(f"  left one-block majorant = {format_fraction(left_one_block_majorant)}")
    print(f"  left one-block majorant (float) = {float(left_one_block_majorant):.12g}")
    print(f"  right one-block majorant = {format_fraction(right_one_block_majorant)}")
    print(f"  right one-block majorant (float) = {float(right_one_block_majorant):.12g}")
    print(f"  combined one-block majorant = {format_fraction(combined_one_block_majorant)}")
    print(f"  combined one-block majorant (float) = {float(combined_one_block_majorant):.12g}")
    print(f"  coprime-branch bound RHS = {format_fraction(coprime_bound_rhs)}")
    print(f"  coprime-branch bound RHS (float) = {float(coprime_bound_rhs):.12g}")
    print()

    print("Immediate diagnostics")
    print(f"  exact abs sum equals crude 3-majorant: {unified_abs_exact_weight == unified_abs_crude_three}")
    if unified_abs_exact_weight != 0:
        print(f"  |unified exact| / unified abs = {float(abs(unified_exact) / unified_abs_exact_weight):.12g}")
    print(f"  max |K(a,b)| on active support = {format_fraction(max_abs_kernel)}")
    print(f"  max |effective weight| on active support = {format_fraction(max_abs_weight)}")
    print()

    print("Signed odd-surface kernel piece audit")
    print("  piece              signed value              absolute value            |signed|/abs")
    for piece in piece_names:
        signed_val = piece_signed[piece]
        abs_val = piece_abs[piece]
        ratio = float(abs(signed_val) / abs_val) if abs_val != 0 else float("nan")
        print(
            f"  {piece:<18}"
            f"{format_fraction(signed_val):>24}  "
            f"{format_fraction(abs_val):>24}  "
            f"{ratio:>12.6g}"
        )
    print()

    print("Swap symmetry diagnostics on weighted signed summands")
    print("  piece              sum|S(a,b)-S(b,a)|       sum|S(a,b)+S(b,a)|       max sym diff           max antisym diff")
    for piece in piece_names:
        print(
            f"  {piece:<18}"
            f"{format_fraction(sym_diff_abs[piece]):>24}  "
            f"{format_fraction(antisym_diff_abs[piece]):>24}  "
            f"{format_fraction(max_sym_diff[piece]):>20}  "
            f"{format_fraction(max_antisym_diff[piece]):>20}"
        )
    print()

    print("Density pair-sign audit")
    print(f"  positive pair summands = {density_pos_count}")
    print(f"  negative pair summands = {density_neg_count}")
    print(f"  zero pair summands = {density_zero_count}")
    print(f"  total positive mass = {format_fraction(density_pos_mass)}")
    print(f"  total positive mass (float) = {float(density_pos_mass):.12g}")
    print(f"  total negative mass = {format_fraction(density_neg_mass)}")
    print(f"  total negative mass (float) = {float(density_neg_mass):.12g}")
    if density_pos_mass + density_neg_mass != 0:
        print(f"  cancellation ratio = {float(abs(piece_signed['density']) / (density_pos_mass + density_neg_mass)):.12g}")
    print()

    print("Top 20 fixed-a density contributors by |T(a)|")
    print("  a        fac             c(a)                  I(a)                        T(a)                    abs row sum         ratio    b-count")
    top_rows = sorted(
        odd_active_support,
        key=lambda a: abs(density_row_contrib[a]),
        reverse=True,
    )[:20]
    for a in top_rows:
        row_ratio = float(abs(density_row_inner[a]) / density_row_abs[a]) if density_row_abs[a] != 0 else float("nan")
        print(
            f"  {a:<8}"
            f"{format_factorization(a, spf):<16}"
            f"{format_fraction(coeff_base(a, mu, phi)):>20}  "
            f"{format_fraction(density_row_inner[a]):>24}  "
            f"{format_fraction(density_row_contrib[a]):>24}  "
            f"{format_fraction(density_row_abs[a]):>20}  "
            f"{row_ratio:>8.4g}  "
            f"{density_row_count[a]:>8}"
        )
    print()

    print("Top 20 density rows with row mass split")
    print("  a        fac             I(a)                        pos mass                    neg mass                    row ratio")
    for a in top_rows:
        row_ratio = float(abs(density_row_inner[a]) / density_row_abs[a]) if density_row_abs[a] != 0 else float("nan")
        print(
            f"  {a:<8}"
            f"{format_factorization(a, spf):<16}"
            f"{format_fraction(density_row_inner[a]):>24}  "
            f"{format_fraction(density_row_pos_mass[a]):>24}  "
            f"{format_fraction(density_row_neg_mass[a]):>24}  "
            f"{row_ratio:>10.6g}"
        )
    print()

    def omega(n: int) -> int:
        return len(factorization(n, spf))

    def smallest_prime_factor(n: int) -> int:
        fac = factorization(n, spf)
        return min(fac) if fac else 1

    def summarize_group(name: str, rows: list[int]) -> None:
        signed = sum((density_row_contrib[a] for a in rows), Fraction(0, 1))
        abs_mass = sum((abs(density_row_contrib[a]) for a in rows), Fraction(0, 1))
        inner_abs = sum((density_row_abs[a] for a in rows), Fraction(0, 1))
        ratio = float(abs(signed) / abs_mass) if abs_mass != 0 else float("nan")
        inner_ratio = float(abs(signed) / inner_abs) if inner_abs != 0 else float("nan")
        print(
            f"  {name:<14} count={len(rows):>4}  "
            f"signed={float(signed):>14.6g}  "
            f"row-abs={float(abs_mass):>14.6g}  "
            f"inner-abs={float(inner_abs):>14.6g}  "
            f"|signed|/row-abs={ratio:>10.4g}  "
            f"|signed|/inner-abs={inner_ratio:>10.4g}"
        )

    print("Grouped summaries by omega(a)")
    omega_values = sorted({omega(a) for a in odd_active_support})
    for w in omega_values:
        summarize_group(f"omega={w}", [a for a in odd_active_support if omega(a) == w])
    print()

    print("Grouped summaries by smallest prime factor")
    spf_values = sorted({smallest_prime_factor(a) for a in odd_active_support})
    for p in spf_values:
        summarize_group(f"spf={p}", [a for a in odd_active_support if smallest_prime_factor(a) == p])
    print()

    print("Grouped summaries by size range")
    size_buckets = [
        ("a<=100", [a for a in odd_active_support if a <= 100]),
        ("100<a<=500", [a for a in odd_active_support if 100 < a <= 500]),
        ("500<a<=1000", [a for a in odd_active_support if 500 < a <= 1000]),
        ("1000<a", [a for a in odd_active_support if a > 1000]),
    ]
    for name, rows in size_buckets:
        summarize_group(name, rows)
    print()

    print("Grouped summaries by sign of c(a)")
    positive_ca = [a for a in odd_active_support if coeff_base(a, mu, phi) > 0]
    negative_ca = [a for a in odd_active_support if coeff_base(a, mu, phi) < 0]
    zero_ca = [a for a in odd_active_support if coeff_base(a, mu, phi) == 0]
    summarize_group("c(a)>0", positive_ca)
    summarize_group("c(a)<0", negative_ca)
    summarize_group("c(a)=0", zero_ca)
    print()

    print("Focused row audits: top contributing b terms in I_density(a)")
    for a in FOCUS_ROWS:
        if a not in density_row_terms:
            print(f"  a = {a}: not present on active odd surface")
            continue
        nonzero_terms = [t for t in density_row_terms[a] if t[3] != 0]
        row_ratio = float(abs(density_row_inner[a]) / density_row_abs[a]) if density_row_abs[a] != 0 else float("nan")
        print(
            f"  a = {a}  fac(a) = {format_factorization(a, spf)}  "
            f"c(a) = {format_fraction(coeff_base(a, mu, phi))}  "
            f"I(a) = {format_fraction(density_row_inner[a])}  "
            f"T(a) = {format_fraction(density_row_contrib[a])}  "
            f"active b count = {density_row_count[a]}  "
            f"nonzero b count = {len(nonzero_terms)}  "
            f"row ratio = {row_ratio:.6g}"
        )
        print("    b        fac(b)          c(b)                  K_density(a,b)                c(b)*K_density(a,b)")
        top_b_terms = sorted(
            density_row_terms[a],
            key=lambda t: abs(t[3]),
            reverse=True,
        )[:20]
        for b, cb, kd, term in top_b_terms:
            print(
                f"    {b:<8}"
                f"{format_factorization(b, spf):<16}"
                f"{format_fraction(cb):>20}  "
                f"{format_fraction(kd):>24}  "
                f"{format_fraction(term):>24}"
            )
        print()

    print("Prime row summary for odd primes a <= 100")
    print("  a        c(a)                  I(a)                        T(a)                    abs row sum         ratio    b-count  nonzero")
    prime_rows = [a for a in odd_active_support if a <= 100 and spf[a] == a and a > 2]
    for a in prime_rows:
        nonzero_terms = sum(1 for _, _, _, term in density_row_terms[a] if term != 0)
        row_ratio = float(abs(density_row_inner[a]) / density_row_abs[a]) if density_row_abs[a] != 0 else float("nan")
        print(
            f"  {a:<8}"
            f"{format_fraction(coeff_base(a, mu, phi)):>20}  "
            f"{format_fraction(density_row_inner[a]):>24}  "
            f"{format_fraction(density_row_contrib[a]):>24}  "
            f"{format_fraction(density_row_abs[a]):>20}  "
            f"{row_ratio:>8.4g}  "
            f"{density_row_count[a]:>8}  "
            f"{nonzero_terms:>7}"
        )
    print()

    def summarize_terms(name: str, terms: list[tuple[int, Fraction, Fraction, Fraction]]) -> None:
        signed = sum((term for _, _, _, term in terms), Fraction(0, 1))
        abs_mass = sum((abs(term) for _, _, _, term in terms), Fraction(0, 1))
        nonzero = sum(1 for _, _, _, term in terms if term != 0)
        ratio = float(abs(signed) / abs_mass) if abs_mass != 0 else float("nan")
        print(
            f"    {name:<12} count={len(terms):>4}  nonzero={nonzero:>4}  "
            f"signed={float(signed):>12.6g}  abs={float(abs_mass):>12.6g}  ratio={ratio:>8.4g}"
        )

    print("Focused class summaries for a = 5")
    a = 5
    if a in density_row_terms:
        terms = density_row_terms[a]
        for r in [0, 1, 2]:
            summarize_terms(f"b mod 3={r}", [t for t in terms if t[0] % 3 == r])
        for r in [0, 1, 2, 3, 4]:
            summarize_terms(f"b mod 5={r}", [t for t in terms if t[0] % 5 == r])
        print("    mod 15 residue summary")
        for r in range(15):
            bucket = [t for t in terms if t[0] % 15 == r]
            if bucket:
                summarize_terms(f"b mod 15={r}", bucket)
        spf_groups = sorted({smallest_prime_factor(b) for b, _, _, _ in terms})
        for p in spf_groups[:12]:
            summarize_terms(f"spf(b)={p}", [t for t in terms if smallest_prime_factor(t[0]) == p])
        print()
        print("Detailed top b terms inside selected mod 15 classes for a = 5")
        selected_residues = [7, 9, 2, 4, 11, 13, 14, 6, 3]
        for r in selected_residues:
            bucket = [t for t in terms if t[0] % 15 == r]
            if not bucket:
                continue
            signed = sum((term for _, _, _, term in bucket), Fraction(0, 1))
            abs_mass = sum((abs(term) for _, _, _, term in bucket), Fraction(0, 1))
            ratio = float(abs(signed) / abs_mass) if abs_mass != 0 else float("nan")
            print(
                f"    class b ≡ {r} (mod 15): count={len(bucket)}  "
                f"signed={float(signed):.6g}  abs={float(abs_mass):.6g}  ratio={ratio:.6g}"
            )
            print(
                "      b        fac(b)          c(b)                  "
                "K_density(5,b)               c(b)*K_density          period   blocks"
            )
            top_bucket = sorted(bucket, key=lambda t: abs(t[3]), reverse=True)[:12]
            for b, cb, kd, term in top_bucket:
                period = centered_ramanujan_pair_block_period(a, b)
                blocks = H1 // period
                print(
                    f"      {b:<8}"
                    f"{format_factorization(b, spf):<16}"
                    f"{format_fraction(cb):>20}  "
                    f"{format_fraction(kd):>24}  "
                    f"{format_fraction(term):>24}  "
                    f"{period:>7}  {blocks:>6}"
                )
    print()

    print("Surrogate normalization with C2_numeric = 1/10")
    print(f"  global pair scale = {format_fraction(PAIR_NORMALIZATION_SURROGATE)}")
    print(f"  unified exact sum (surrogate) = {format_fraction(PAIR_NORMALIZATION_SURROGATE * unified_exact)}")
    print(f"  unified exact sum (surrogate float) = {float(PAIR_NORMALIZATION_SURROGATE * unified_exact):.12g}")
    print(f"  unified abs sum (surrogate) = {format_fraction(PAIR_NORMALIZATION_SURROGATE * unified_abs_exact_weight)}")
    print(f"  unified abs sum (surrogate float) = {float(PAIR_NORMALIZATION_SURROGATE * unified_abs_exact_weight):.12g}")
    print(f"  endpoint total abs (surrogate float) = {float(PAIR_NORMALIZATION_SURROGATE * (abs(endpoint_one_two) + abs(endpoint_two_one))):.12g}")
    print(f"  one-block majorant total (surrogate float) = {float(PAIR_NORMALIZATION_SURROGATE * combined_one_block_majorant):.12g}")
    print(f"  coprime-branch bound RHS (surrogate float) = {float(PAIR_NORMALIZATION_SURROGATE * coprime_bound_rhs):.12g}")


if __name__ == "__main__":
    main()
