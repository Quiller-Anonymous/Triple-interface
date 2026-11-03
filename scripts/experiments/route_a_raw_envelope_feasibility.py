"""Floating-point raw-envelope feasibility study; this is not a proof.

Uses the repository numerical harness and the Python standard library.
Each output line is a JSON record for one window.
"""
import json
import math
from exp_q0_minor_singularity_exact_harness import (
    H, Q0, major_zero_mode, mobius_phi_sieve, q0_norm_factor,
    sieve_primes_mask, sum_by_s,
)
from exp_q0_minor_zero_mode_refinement import sum_by_s_uniform_fast

KAPPA = 0.32713386268984  # Floating approximation to the frozen candidate.


def normalized_sigma(n, primes):
    """Product of (p-1)/(p-2) over odd prime divisors of n."""
    value = 1.0
    for p in primes:
        if p * p > n:
            break
        if n % p == 0:
            if p > 2:
                value *= (p - 1) / (p - 2)
            while n % p == 0:
                n //= p
    if n > 2:
        value *= (n - 1) / (n - 2)
    return value


def window_record(x, phi, primes, prime_mask):
    raw = sum_by_s(x)
    geometric = sum_by_s_uniform_fast(x)
    ns = list(range(x + x % 2, x + H + 1, 2))
    m = len(ns)
    normalizer = 1 / (math.log(x) * (2 * H + 1)) ** 2
    floor = q0_norm_factor(x + H)
    weight = 1 - major_zero_mode(x, phi)
    baselines, zeros = [], []
    for n in ns:
        q = q0_norm_factor(n)
        # Preserve both q factors and the geometric normalization.
        baselines.append(q * q * weight * normalizer * geometric[n]
                         * normalized_sigma(n, primes))
        zeros.append(q * weight * raw.get(n, 0.0))
    errors = [z - KAPPA * floor * b for z, b in zip(zeros, baselines)]
    scaled_errors = [e / floor for e in errors]
    mean = math.fsum(scaled_errors) / m
    energy = math.fsum(e * e for e in scaled_errors)
    effective_c3 = energy * H * Q0**2
    assert effective_c3 < 4, "Sample fails the proposed C3=4 budget"
    return {
        "X": x,
        "X_is_twice_prime": bool(prime_mask[x // 2])
        if x % 2 == 0 and x // 2 < len(prime_mask) else False,
        "m": m,
        "w0": weight,
        "cX": floor,
        "raw_error_energy": math.fsum(e * e for e in errors),
        "raw_error_energy_over_cX2": energy,
        "scaled_zero_energy": math.fsum((z / floor) ** 2 for z in zeros),
        "scaled_baseline_energy": math.fsum((KAPPA * b) ** 2 for b in baselines),
        "scaled_error_mean": mean,
        "scaled_error_mean_energy": m * mean * mean,
        "scaled_error_variance_energy": math.fsum((e - mean) ** 2 for e in scaled_errors),
        "equiv_C3_at_window": effective_c3,
        "diagonal_raw_error_scaled": scaled_errors[0],
        "max_baseline_to_zero_ratio": max(
            abs(KAPPA * floor * b / z) for z, b in zip(zeros, baselines) if z),
    }


def main():
    _, phi = mobius_phi_sieve(Q0)
    prime_mask = sieve_primes_mask(5_010_000)
    primes = [n for n in range(2, 4000) if prime_mask[n]]
    p = next(n for n in range(500_000, 510_000) if prime_mask[n])
    for x in [1_000_000, 2 * p, 3_000_000, 10_000_000]:
        print(json.dumps(window_record(x, phi, primes, prime_mask)), flush=True)


if __name__ == "__main__":
    main()
