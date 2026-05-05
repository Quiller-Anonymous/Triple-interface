#!/usr/bin/env python3
"""
Exact audit of the clean supported non-coprime branch on the current Lean surface.

Lean objects matched here:

  centeredRamanujanPairCleanPeriodicSupportedNonCoprimeDefectUpToQ0
  centeredRamanujanPairCleanPeriodicSupportedNonCoprimeCommonPrimeUpToQ0
  centeredRamanujanPairCleanPeriodicSupportedNonCoprimeGcdCorrectionPreferredBranchwiseUpToQ0
  centeredRamanujanPairCleanPeriodicSupportedNonCoprimeRemainderUpToQ0

This is not the earlier scalar-free coprime odd-surface audit. It works directly on the
clean supported non-coprime branch, whose support is the exact one-variable clean support
used in Lean.
"""

from __future__ import annotations

import argparse
import math
from fractions import Fraction


H = 10_000
H1 = H + 1
Q0 = 30_000


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
        pieces.append(str(p) if e == 1 else f"{p}^{e}")
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


def merge_factorizations(a: dict[int, int], b: dict[int, int]) -> dict[int, int]:
    out = dict(a)
    for p, e in b.items():
        out[p] = out.get(p, 0) + e
    return out


def totient_from_factorization(fac: dict[int, int]) -> int:
    out = 1
    for p, e in fac.items():
        out *= (p - 1) * (p ** (e - 1))
    return out


def ceil_div(n: int, d: int) -> int:
    return (n + d - 1) // d


def centered_ramanujan_pair_block_period(q: int, q2: int) -> int:
    return 2 * math.lcm(q, q2)


def even_ramanujan_block_count(q: int, q2: int) -> int:
    return math.lcm(q, q2)


def is_even_nat(n: int) -> bool:
    return n % 2 == 0


def one_variable_clean_support(q: int, spf: list[int]) -> bool:
    if q <= 0 or q % 2 != 0:
        return False
    odd_part = q
    while odd_part % 2 == 0:
        odd_part //= 2
    fac = factorization(odd_part, spf)
    return all(e >= 2 for e in fac.values())


def ramanujan_gcd_class_coeff(q: int, g: int, mu: list[int], phi: list[int]) -> Fraction:
    return Fraction(mu[q // g] * phi[g], 1)


def format_fraction(fr: Fraction) -> str:
    if fr.denominator == 1:
        return str(fr.numerator)
    return f"{fr.numerator}/{fr.denominator}"


def main() -> None:
    ap = argparse.ArgumentParser(description="Exact clean supported non-coprime audit.")
    ap.add_argument("--X", type=int, default=1_000_000)
    ap.add_argument("--Q0", type=int, default=Q0)
    ap.add_argument(
        "--fast-totals",
        action="store_true",
        help="Only compute exact totals and grouped summaries; skip per-pair detail tables.",
    )
    ap.add_argument(
        "--top-pairs",
        type=int,
        default=0,
        help="Optional number of top pairs by |clean defect| to print in detail mode.",
    )
    ap.add_argument(
        "--gcd-report-limit",
        type=int,
        default=20,
        help="Number of exact gcd groups to print in the gcd report.",
    )
    ap.add_argument(
        "--detail-gcd",
        type=int,
        default=0,
        help="Restrict detailed pair output to one exact gcd group.",
    )
    ap.add_argument(
        "--gcd-pattern-scan",
        action="store_true",
        help="Print multiplier-pattern summaries for exact gcd groups, sorted by total mass.",
    )
    ap.add_argument(
        "--residual-pattern-scan",
        action="store_true",
        help="Print multiplier-pattern summaries restricted to the residual non-coprime piece.",
    )
    args = ap.parse_args()

    X = args.X
    q0 = args.Q0

    mu, phi = mobius_phi_sieve(q0)
    spf = spf_sieve(q0)

    support = [q for q in range(1, q0 + 1) if one_variable_clean_support(q, spf)]
    divisors_cache: dict[int, list[int]] = {
        q: divisors_from_factorization(factorization(q, spf)) for q in support
    }
    factor_cache: dict[int, dict[int, int]] = {q: factorization(q, spf) for q in support}
    active_even_divisors_cache: dict[int, list[int]] = {
        q: [g for g in divisors_cache[q] if is_even_nat(g) and mu[q // g] != 0] for q in support
    }

    def raw_even_totient_comparison(q: int, q2: int, g: int, h: int) -> Fraction:
        A = q // g
        B = q2 // h
        fac_ab = merge_factorizations(factor_cache.setdefault(A, factorization(A, spf)), factor_cache.setdefault(B, factorization(B, spf)))
        phi_ab = totient_from_factorization(fac_ab)
        P = centered_ramanujan_pair_block_period(q, q2)
        pair_start = ceil_div(X, math.lcm(g, h))
        pair_len = ((X + P - 1) // math.lcm(g, h) + 1) - pair_start
        pair_rem = sum(
            1
            for t in range(pair_len % (A * B))
            if math.gcd(A * B, pair_start + (pair_len // (A * B)) * (A * B) + t) == 1
        )
        left_start = ceil_div(X, g)
        left_len = ((X + P - 1) // g + 1) - left_start
        left_rem = sum(
            1
            for t in range(left_len % A)
            if math.gcd(A, left_start + (left_len // A) * A + t) == 1
        )
        right_start = ceil_div(X, h)
        right_len = ((X + P - 1) // h + 1) - right_start
        right_rem = sum(
            1
            for t in range(right_len % B)
            if math.gcd(B, right_start + (right_len // B) * B + t) == 1
        )
        pair_main = Fraction((pair_len // (A * B)) * phi_ab + pair_rem, 1)
        side_main = Fraction((left_len // A) * phi[A] + left_rem, 1) * Fraction(
            (right_len // B) * phi[B] + right_rem, 1
        )
        return pair_main - side_main / even_ramanujan_block_count(q, q2)

    def raw_even_coefficient_mismatch(q: int, q2: int, g: int, h: int) -> Fraction:
        A = q // g
        B = q2 // h
        P = centered_ramanujan_pair_block_period(q, q2)
        pair_len = ((X + P - 1) // math.lcm(g, h) + 1) - ceil_div(X, math.lcm(g, h))
        left_len = ((X + P - 1) // g + 1) - ceil_div(X, g)
        right_len = ((X + P - 1) // h + 1) - ceil_div(X, h)
        return Fraction(phi[A] * phi[B], 1) * (
            Fraction(pair_len // (A * B), 1)
            - Fraction((left_len // A) * (right_len // B), even_ramanujan_block_count(q, q2))
        )

    def raw_even_common_prime_overlap(q: int, q2: int, g: int, h: int) -> Fraction:
        A = q // g
        B = q2 // h
        P = centered_ramanujan_pair_block_period(q, q2)
        pair_len = ((X + P - 1) // math.lcm(g, h) + 1) - ceil_div(X, math.lcm(g, h))
        gcd_ab = math.gcd(A, B)
        return Fraction(phi[A] * phi[B], 1) * Fraction(pair_len // (A * B), 1) * (
            Fraction(gcd_ab, phi[gcd_ab]) - 1
        )

    def raw_even_remainder(q: int, q2: int, g: int, h: int) -> Fraction:
        return (
            raw_even_totient_comparison(q, q2, g, h)
            - raw_even_coefficient_mismatch(q, q2, g, h)
            - raw_even_common_prime_overlap(q, q2, g, h)
        )

    def pair_terms(q: int, q2: int) -> tuple[Fraction, Fraction, Fraction]:
        block_scalar = H1 // centered_ramanujan_pair_block_period(q, q2)
        defect = Fraction(0, 1)
        common = Fraction(0, 1)
        rem = Fraction(0, 1)
        scale = Fraction(block_scalar, 1)
        for g in active_even_divisors_cache[q]:
            cg = ramanujan_gcd_class_coeff(q, g, mu, phi)
            for h in active_even_divisors_cache[q2]:
                ch = ramanujan_gcd_class_coeff(q2, h, mu, phi)
                pref = cg * ch * scale
                tot_point = raw_even_totient_comparison(q, q2, g, h)
                common_point = raw_even_common_prime_overlap(q, q2, g, h)
                rem_point = tot_point - raw_even_coefficient_mismatch(q, q2, g, h) - common_point
                defect += pref * tot_point
                common += pref * common_point
                rem += pref * rem_point
        return defect, common, rem

    def gcd_base_weight(q: int, q2: int, g: int, h: int) -> Fraction:
        block_scalar = H1 // centered_ramanujan_pair_block_period(q, q2)
        return (
            ramanujan_gcd_class_coeff(q, g, mu, phi)
            * ramanujan_gcd_class_coeff(q2, h, mu, phi)
            * Fraction(block_scalar * phi[q // g] * phi[q2 // h], 1)
        )

    def gcd_weight_at_gcd(q: int, q2: int, d: int) -> Fraction:
        total = Fraction(0, 1)
        for g in active_even_divisors_cache[q]:
            for h in active_even_divisors_cache[q2]:
                if math.gcd(g, h) == d:
                    total += gcd_base_weight(q, q2, g, h)
        return total

    def gcd_half_total_product(q: int, q2: int) -> Fraction:
        G = math.gcd(q, q2)
        total = Fraction(0, 1)
        aq = 2 * (q // G)
        bq = 2 * (q2 // G)
        divs_a = divisors_from_factorization(factorization(aq, spf))
        divs_b = divisors_from_factorization(factorization(bq, spf))
        for a in divs_a:
            for b in divs_b:
                total += gcd_base_weight(q, q2, (G // 2) * a, (G // 2) * b)
        return total

    def gcd_preferred_branchwise_term(q: int, q2: int) -> Fraction:
        G = math.gcd(q, q2)
        small = Fraction(0, 1)
        divisors_G = divisors_from_factorization(factorization(G, spf))
        for d in divisors_G:
            if 2 * d < G:
                small += gcd_weight_at_gcd(q, q2, d) * (Fraction(0, 1) - Fraction(4, G))
        if G % 4 == 0:
            return small + gcd_weight_at_gcd(q, q2, G) + gcd_half_total_product(q, q2) * (Fraction(1, 1) - Fraction(4, G))
        return small + gcd_weight_at_gcd(q, q2, G) * (Fraction(2, 1) - Fraction(4, G))

    keep_pair_details = (not args.fast_totals) and args.top_pairs > 0
    pairs: list[tuple[int, int, Fraction, Fraction, Fraction, Fraction]] = []
    pair_count = 0
    defect_total = Fraction(0, 1)
    common_total = Fraction(0, 1)
    gcd_total = Fraction(0, 1)
    rem_total = Fraction(0, 1)
    defect_abs = Fraction(0, 1)
    common_abs = Fraction(0, 1)
    gcd_abs = Fraction(0, 1)
    rem_abs = Fraction(0, 1)
    diagonal_total = Fraction(0, 1)
    offdiag_total = Fraction(0, 1)
    diagonal_abs = Fraction(0, 1)
    offdiag_abs = Fraction(0, 1)
    piece_totals: dict[str, dict[str, Fraction]] = {
        "diagonal": {
            "signed": Fraction(0, 1),
            "abs": Fraction(0, 1),
            "common": Fraction(0, 1),
            "gcd_pref": Fraction(0, 1),
            "rem": Fraction(0, 1),
        },
        "dyadic": {
            "signed": Fraction(0, 1),
            "abs": Fraction(0, 1),
            "common": Fraction(0, 1),
            "gcd_pref": Fraction(0, 1),
            "rem": Fraction(0, 1),
        },
        "residual": {
            "signed": Fraction(0, 1),
            "abs": Fraction(0, 1),
            "common": Fraction(0, 1),
            "gcd_pref": Fraction(0, 1),
            "rem": Fraction(0, 1),
        },
    }
    theorem_piece_order = (
        "diagonal",
        "dyadic",
        "1:4",
        "1:8",
        "1:3",
        "1:9",
        "1:16",
        "1:5",
        "1:32",
        "1:6",
        "2:3",
        "1:10",
        "2:5",
        "tail2",
    )
    theorem_piece_totals: dict[str, dict[str, Fraction]] = {
        piece: {
            "signed": Fraction(0, 1),
            "abs": Fraction(0, 1),
            "common": Fraction(0, 1),
            "gcd_pref": Fraction(0, 1),
            "rem": Fraction(0, 1),
        }
        for piece in theorem_piece_order
    }
    gcd_groups: dict[int, dict[str, Fraction | int]] = {}
    odd_shared_prime_groups: dict[str, tuple[Fraction, Fraction, int]] = {}
    multiplier_groups: dict[tuple[int, int], tuple[Fraction, Fraction, int]] = {}
    gcd_pattern_groups: dict[int, dict[str, object]] = {}
    residual_pattern_groups: dict[tuple[int, int], dict[str, Fraction | int]] = {}

    for i, q in enumerate(support):
        for q2 in support[i:]:
            if math.gcd(q, q2) == 1:
                continue
            pair_count += 1
            defect, common, rem = pair_terms(q, q2)
            gcd_pref = gcd_preferred_branchwise_term(q, q2)
            G = math.gcd(q, q2)
            if keep_pair_details and (args.detail_gcd == 0 or G == args.detail_gcd):
                pairs.append((q, q2, defect, common, gcd_pref, rem))
            mult = 1 if q == q2 else 2
            defect_total += mult * defect
            common_total += mult * common
            gcd_total += mult * gcd_pref
            rem_total += mult * rem
            defect_abs += mult * abs(defect)
            common_abs += mult * abs(common)
            gcd_abs += mult * abs(gcd_pref)
            rem_abs += mult * abs(rem)
            if q == q2:
                piece = "diagonal"
            elif q2 == 2 * q or q == 2 * q2:
                piece = "dyadic"
            else:
                piece = "residual"
            if piece == "residual":
                m = q // G
                n = q2 // G
                pattern = (min(m, n), max(m, n))
                if pattern == (1, 4):
                    theorem_piece = "1:4"
                elif pattern == (1, 8):
                    theorem_piece = "1:8"
                elif pattern == (1, 3):
                    theorem_piece = "1:3"
                elif pattern == (1, 9):
                    theorem_piece = "1:9"
                elif pattern == (1, 16):
                    theorem_piece = "1:16"
                elif pattern == (1, 5):
                    theorem_piece = "1:5"
                elif pattern == (1, 32):
                    theorem_piece = "1:32"
                elif pattern == (1, 6):
                    theorem_piece = "1:6"
                elif pattern == (2, 3):
                    theorem_piece = "2:3"
                elif pattern == (1, 10):
                    theorem_piece = "1:10"
                elif pattern == (2, 5):
                    theorem_piece = "2:5"
                else:
                    theorem_piece = "tail2"
            else:
                theorem_piece = piece
            piece_totals[piece]["signed"] += mult * defect
            piece_totals[piece]["abs"] += mult * abs(defect)
            piece_totals[piece]["common"] += mult * common
            piece_totals[piece]["gcd_pref"] += mult * gcd_pref
            piece_totals[piece]["rem"] += mult * rem
            theorem_piece_totals[theorem_piece]["signed"] += mult * defect
            theorem_piece_totals[theorem_piece]["abs"] += mult * abs(defect)
            theorem_piece_totals[theorem_piece]["common"] += mult * common
            theorem_piece_totals[theorem_piece]["gcd_pref"] += mult * gcd_pref
            theorem_piece_totals[theorem_piece]["rem"] += mult * rem
            if args.residual_pattern_scan and piece == "residual":
                if pattern not in residual_pattern_groups:
                    residual_pattern_groups[pattern] = {
                        "signed": Fraction(0, 1),
                        "abs": Fraction(0, 1),
                        "common": Fraction(0, 1),
                        "gcd_pref": Fraction(0, 1),
                        "rem": Fraction(0, 1),
                        "count": 0,
                    }
                rdata = residual_pattern_groups[pattern]
                rdata["signed"] += mult * defect
                rdata["abs"] += mult * abs(defect)
                rdata["common"] += mult * common
                rdata["gcd_pref"] += mult * gcd_pref
                rdata["rem"] += mult * rem
                rdata["count"] += mult
            if q == q2:
                diagonal_total += defect
                diagonal_abs += abs(defect)
            else:
                offdiag_total += 2 * defect
                offdiag_abs += 2 * abs(defect)
            if args.detail_gcd and G == args.detail_gcd:
                m = q // G
                n = q2 // G
                msigned, mabs, mcount = multiplier_groups.get((m, n), (Fraction(0, 1), Fraction(0, 1), 0))
                multiplier_groups[(m, n)] = (msigned + defect, mabs + abs(defect), mcount + 1)
            if args.gcd_pattern_scan:
                m = q // G
                n = q2 // G
                if G not in gcd_pattern_groups:
                    gcd_pattern_groups[G] = {
                        "pairs": {},
                        "diag": Fraction(0, 1),
                        "diag_abs": Fraction(0, 1),
                        "dyadic": Fraction(0, 1),
                        "dyadic_abs": Fraction(0, 1),
                        "other": Fraction(0, 1),
                        "other_abs": Fraction(0, 1),
                    }
                pdata = gcd_pattern_groups[G]
                pair_map = pdata["pairs"]
                assert isinstance(pair_map, dict)
                psigned, pabs, pcount = pair_map.get((m, n), (Fraction(0, 1), Fraction(0, 1), 0))
                pair_map[(m, n)] = (psigned + defect, pabs + abs(defect), pcount + 1)
                if (m, n) == (1, 1):
                    pdata["diag"] += defect
                    pdata["diag_abs"] += abs(defect)
                elif (m, n) == (1, 2):
                    pdata["dyadic"] += defect
                    pdata["dyadic_abs"] += abs(defect)
                else:
                    pdata["other"] += defect
                    pdata["other_abs"] += abs(defect)
            if G not in gcd_groups:
                gcd_groups[G] = {
                    "signed": Fraction(0, 1),
                    "abs": Fraction(0, 1),
                    "common": Fraction(0, 1),
                    "gcd_pref": Fraction(0, 1),
                    "rem": Fraction(0, 1),
                    "diag_signed": Fraction(0, 1),
                    "diag_abs": Fraction(0, 1),
                    "off_signed": Fraction(0, 1),
                    "off_abs": Fraction(0, 1),
                    "count": 0,
                }
            gdata = gcd_groups[G]
            gdata["signed"] += mult * defect
            gdata["abs"] += mult * abs(defect)
            gdata["common"] += mult * common
            gdata["gcd_pref"] += mult * gcd_pref
            gdata["rem"] += mult * rem
            gdata["count"] += mult
            if q == q2:
                gdata["diag_signed"] += defect
                gdata["diag_abs"] += abs(defect)
            else:
                gdata["off_signed"] += 2 * defect
                gdata["off_abs"] += 2 * abs(defect)
            odd_g = G
            while odd_g % 2 == 0:
                odd_g //= 2
            if odd_g == 1:
                label = "2-only"
            else:
                label = str(min(factorization(odd_g, spf)))
            ssigned, sabs, scount = odd_shared_prime_groups.get(label, (Fraction(0, 1), Fraction(0, 1), 0))
            odd_shared_prime_groups[label] = (ssigned + mult * defect, sabs + mult * abs(defect), scount + mult)

    print("Clean supported non-coprime audit")
    print(f"  X = {X}")
    print(f"  Q0 = {q0}")
    print(f"  support size = {len(support)}")
    print(f"  support sum = {sum(support)}")
    print(f"  unordered non-coprime pairs = {pair_count}")
    print(f"  ordered non-coprime pairs = {2 * pair_count - len(support)}")
    print()

    print("Exact branch values")
    print(f"  clean defect signed = {format_fraction(defect_total)}")
    print(f"  clean defect signed (float) = {float(defect_total):.12g}")
    print(f"  clean defect abs = {format_fraction(defect_abs)}")
    print(f"  clean defect abs (float) = {float(defect_abs):.12g}")
    print(f"  |signed| / abs = {float(abs(defect_total) / defect_abs) if defect_abs else float('nan'):.12g}")
    print()
    print(f"  common-prime signed = {format_fraction(common_total)}")
    print(f"  common-prime abs (float) = {float(common_abs):.12g}")
    print(f"  gcd-preferred signed = {format_fraction(gcd_total)}")
    print(f"  gcd-preferred abs (float) = {float(gcd_abs):.12g}")
    print(f"  remainder signed = {format_fraction(rem_total)}")
    print(f"  remainder abs (float) = {float(rem_abs):.12g}")
    print()

    print("Diagonal / dyadic / residual split")
    print("  piece       signed          abs             ratio       common       gcdPref      rem")
    for piece in ("diagonal", "dyadic", "residual"):
        data = piece_totals[piece]
        signed = data["signed"]
        mass = data["abs"]
        ratio = float(abs(signed) / mass) if mass else float("nan")
        print(
            f"  {piece:<10}"
            f"{float(signed):>13.6g}  "
            f"{float(mass):>13.6g}  "
            f"{ratio:>9.6g}  "
            f"{float(data['common']):>11.6g}  "
            f"{float(data['gcd_pref']):>11.6g}  "
            f"{float(data['rem']):>11.6g}"
        )
    print()

    print("Diagonal / dyadic / multiplier-pattern / tail split")
    print("  piece       signed          abs             ratio       common       gcdPref      rem")
    for piece in theorem_piece_order:
        data = theorem_piece_totals[piece]
        signed = data["signed"]
        mass = data["abs"]
        ratio = float(abs(signed) / mass) if mass else float("nan")
        print(
            f"  {piece:<10}"
            f"{float(signed):>13.6g}  "
            f"{float(mass):>13.6g}  "
            f"{ratio:>9.6g}  "
            f"{float(data['common']):>11.6g}  "
            f"{float(data['gcd_pref']):>11.6g}  "
            f"{float(data['rem']):>11.6g}"
        )
    print()

    print("Diagonal vs off-diagonal")
    print(f"  diagonal signed (float) = {float(diagonal_total):.12g}")
    print(f"  diagonal abs (float) = {float(diagonal_abs):.12g}")
    print(f"  off-diagonal signed (float) = {float(offdiag_total):.12g}")
    print(f"  off-diagonal abs (float) = {float(offdiag_abs):.12g}")
    print()

    print("By gcd(q,q')")
    print("  gcd     signed          abs             ratio      diag         off          common       gcdPref      rem          count")
    gcd_items = sorted(
        gcd_groups.items(),
        key=lambda kv: kv[1]["abs"],  # type: ignore[index]
        reverse=True,
    )
    for G, data in gcd_items[: args.gcd_report_limit]:
        signed = data["signed"]  # type: ignore[index]
        mass = data["abs"]  # type: ignore[index]
        ratio = float(abs(signed) / mass) if mass else float("nan")
        print(
            f"  {G:<6}"
            f"{float(signed):>13.6g}  "
            f"{float(mass):>13.6g}  "
            f"{ratio:>9.6g}  "
            f"{float(data['diag_signed']):>11.6g}  "
            f"{float(data['off_signed']):>11.6g}  "
            f"{float(data['common']):>11.6g}  "
            f"{float(data['gcd_pref']):>11.6g}  "
            f"{float(data['rem']):>11.6g}  "
            f"{int(data['count']):>8}"
        )
    print()

    print("By smallest odd shared prime")
    print("  tag      signed            abs               ratio        count")
    def odd_key(item: tuple[str, tuple[Fraction, Fraction, int]]) -> tuple[int, float]:
        label, (_, mass, _) = item
        primary = 10**9 if label == "2-only" else int(label)
        return (primary, -float(mass))
    for label, (signed, mass, count) in sorted(odd_shared_prime_groups.items(), key=lambda kv: kv[1][1], reverse=True)[:12]:
        ratio = float(abs(signed) / mass) if mass else float("nan")
        print(f"  {label:<8}{float(signed):>14.6g}  {float(mass):>14.6g}  {ratio:>10.6g}  {count:>8}")
    print()

    if args.residual_pattern_scan:
        print("Residual multiplier-pattern scan")
        print("  pattern   signed          abs             ratio       common       gcdPref      rem          count")
        residual_items = sorted(
            residual_pattern_groups.items(),
            key=lambda kv: kv[1]["abs"],  # type: ignore[index]
            reverse=True,
        )
        for (m, n), data in residual_items[: max(args.gcd_report_limit, 20)]:
            signed = data["signed"]  # type: ignore[index]
            mass = data["abs"]  # type: ignore[index]
            ratio = float(abs(signed) / mass) if mass else float("nan")
            print(
                f"  {m}:{n:<7}"
                f"{float(signed):>13.6g}  "
                f"{float(mass):>13.6g}  "
                f"{ratio:>9.6g}  "
                f"{float(data['common']):>11.6g}  "
                f"{float(data['gcd_pref']):>11.6g}  "
                f"{float(data['rem']):>11.6g}  "
                f"{int(data['count']):>8}"
            )
        print()

    if args.gcd_pattern_scan:
        print("Exact gcd multiplier-pattern scan")
        print("  gcd     abs             signed          nzPairs  diagAbs       dyadicAbs     otherAbs      other?   nonzero (m,n)")
        for G, data in gcd_items[: args.gcd_report_limit]:
            mass = data["abs"]  # type: ignore[index]
            signed = data["signed"]  # type: ignore[index]
            pdata = gcd_pattern_groups.get(G)
            if pdata is None:
                continue
            pair_map = pdata["pairs"]
            assert isinstance(pair_map, dict)
            nonzero_pairs = [
                (mn, vals) for mn, vals in pair_map.items()
                if vals[1] != 0
            ]
            nonzero_pairs.sort(key=lambda item: item[1][1], reverse=True)
            pair_labels = ",".join(f"{mn[0]}:{mn[1]}" for mn, _ in nonzero_pairs[:8])
            other_abs = pdata["other_abs"]
            assert isinstance(other_abs, Fraction)
            print(
                f"  {G:<6}"
                f"{float(mass):>13.6g}  "
                f"{float(signed):>13.6g}  "
                f"{len(nonzero_pairs):>7}  "
                f"{float(pdata['diag_abs']):>11.6g}  "
                f"{float(pdata['dyadic_abs']):>11.6g}  "
                f"{float(other_abs):>11.6g}  "
                f"{('yes' if other_abs else 'no'):>7}   "
                f"{pair_labels}"
            )
        print()

    if keep_pair_details:
        if args.detail_gcd:
            G = args.detail_gcd
            if G in gcd_groups:
                data = gcd_groups[G]
                print(f"Detail for exact gcd G = {G}")
                print(f"  signed      = {float(data['signed']):.12g}")
                print(f"  abs         = {float(data['abs']):.12g}")
                print(f"  ratio       = {float(abs(data['signed']) / data['abs']) if data['abs'] else float('nan'):.12g}")
                print(f"  diagonal    = {float(data['diag_signed']):.12g}")
                print(f"  offdiag     = {float(data['off_signed']):.12g}")
                print(f"  common      = {float(data['common']):.12g}")
                print(f"  gcdPref     = {float(data['gcd_pref']):.12g}")
                print(f"  remainder   = {float(data['rem']):.12g}")
                print(f"  pair count  = {int(data['count'])}")
                print()
                print("Top multiplier pairs (m,n) with q=Gm, q'=Gn")
                print("  m       n       signed          abs             ratio        count")
                for (m, n), (signed, mass, count) in sorted(multiplier_groups.items(), key=lambda kv: kv[1][1], reverse=True)[: min(20, len(multiplier_groups))]:
                    ratio = float(abs(signed) / mass) if mass else float("nan")
                    print(f"  {m:<8}{n:<8}{float(signed):>12.6g}  {float(mass):>12.6g}  {ratio:>10.6g}  {count:>8}")
                print()
        top_n = min(args.top_pairs, len(pairs))
        if args.detail_gcd:
            print(f"Top {top_n} pairs by |clean defect| inside gcd={args.detail_gcd}")
        else:
            print(f"Top {top_n} pairs by |clean defect|")
        print("  q       q'      fac(q)           fac(q')          defect            common            gcdPref           rem")
        for q, q2, defect, common, gcd_pref, rem in sorted(pairs, key=lambda t: abs(t[2]), reverse=True)[:top_n]:
            print(
                f"  {q:<7}{q2:<8}"
                f"{format_factorization(q, spf):<17}"
                f"{format_factorization(q2, spf):<17}"
                f"{float(defect):>12.6g}  "
                f"{float(common):>12.6g}  "
                f"{float(gcd_pref):>12.6g}  "
                f"{float(rem):>12.6g}"
            )


if __name__ == "__main__":
    main()
