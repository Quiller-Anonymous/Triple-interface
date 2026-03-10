from __future__ import annotations

"""
Shared helpers for the ε₁ minor certificate scripts.

The routines in this module evaluate the current Route-A SSU and exact zero-mode Type-I
expressions at a fixed `X`. They are useful for candidate calibration and generator plumbing, but
they are not yet a fully rigorous proof backend: transcendental quantities are still evaluated with
standard floating-point math.
"""

from dataclasses import dataclass
import math


X0 = 1_000_000
H = 10_000
Q0 = 30_000
Q_SMALL = 12
RX_CONST = 1.5


@dataclass(frozen=True)
class WindowMasses:
    coeff_mass: float
    diag_mass_even: list[float]
    even_ns: list[int]


def sieve_primes_mask(n: int) -> bytearray:
    is_prime = bytearray(b"\x01") * (n + 1)
    is_prime[0:2] = b"\x00\x00"
    limit = int(n**0.5)
    for p in range(2, limit + 1):
        if is_prime[p]:
            start = p * p
            is_prime[start : n + 1 : p] = b"\x00" * (((n - start) // p) + 1)
    return is_prime


def w_scale(x: int) -> float:
    return 1.0 / (math.log(x) * (2 * H + 1))


def prime_window_logsquared(x: int) -> list[tuple[int, float]]:
    lo = x // 2 - H
    hi = x // 2 + H
    is_prime = sieve_primes_mask(hi)
    return [(n, math.log(n) ** 2) for n in range(lo, hi + 1) if is_prime[n]]


def window_masses(x: int) -> WindowMasses:
    data = prime_window_logsquared(x)
    scale = w_scale(x)
    coeff_mass = (scale * scale) * sum(v for _, v in data)
    conv: dict[int, float] = {}
    for n, vn in data:
      for m, vm in data:
          s = n + m
          if x <= s <= x + H and (s & 1) == 0:
              conv[s] = conv.get(s, 0.0) + vn * vm
    even_ns = list(range(x, x + H + 1, 2))
    diag_mass_even = [(scale ** 4) * conv.get(n, 0.0) for n in even_ns]
    return WindowMasses(coeff_mass=coeff_mass, diag_mass_even=diag_mass_even, even_ns=even_ns)


def totients_up_to(n: int) -> list[int]:
    phi = list(range(n + 1))
    for p in range(2, n + 1):
        if phi[p] == p:
            for k in range(p, n + 1, p):
                phi[k] -= phi[k] // p
    return phi


def mobius_sieve(n: int) -> list[int]:
    mu = [1] * (n + 1)
    is_prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if is_prime[p]:
            for k in range(p, n + 1, p):
                is_prime[k] = False
                mu[k] *= -1
            p2 = p * p
            if p2 <= n:
                for k in range(p2, n + 1, p2):
                    mu[k] = 0
    mu[0] = 0
    return mu


def prefix_mertens_over_m(mu: list[int]) -> list[float]:
    acc = 0.0
    out = [0.0] * len(mu)
    for m in range(1, len(mu)):
        acc += float(mu[m]) / float(m)
        out[m] = acc
    return out


def build_s_all(*, q0: int, t_max: int, mu: list[int]) -> list[float]:
    mertens = prefix_mertens_over_m(mu)
    coeff = [0.0] * (q0 + 1)
    for d in range(1, q0 + 1):
        coeff[d] = mertens[q0 // d]
    out = [0.0] * (t_max + 1)
    for d in range(1, q0 + 1):
        cd = coeff[d]
        for t in range(d, t_max + 1, d):
            out[t] += cd
    return out


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def exact_major_zero_mode(x: int) -> float:
    phi = totients_up_to(Q0)
    return (1.0 / x) + (2.0 / x) * sum(phi[q] / q for q in range(2, Q0 + 1))


def route_a_kernel_masses(x: int) -> tuple[float, float]:
    n_max = x + H
    mu = mobius_sieve(Q0)
    phi = totients_up_to(Q0)
    s_all = build_s_all(q0=Q0, t_max=n_max, mu=mu)
    scale_lin = 2.0 / float(x)

    sum_sq_pos_even = 0.0
    sum_sq_pos_odd = 0.0
    for t in range(1, n_max + 1):
        s_small_over_q = 0.0
        ax_rest = 0.0
        inv_pi_t = 1.0 / (math.pi * float(t))
        two_pi_t_over_x = 2.0 * math.pi * t / x
        for q in range(1, Q_SMALL + 1):
            cq = ramanujan_sum(q, t, mu, phi)
            if cq:
                s_small_over_q += cq / q
                if q >= 2:
                    ax_rest += cq * math.sin(two_pi_t_over_x / q) * inv_pi_t
        theta = two_pi_t_over_x
        denom = 2.0 * math.pi * float(t)
        q1_re = math.sin(theta) / denom
        q1_im = -(math.cos(theta) - 1.0) / denom
        lx = scale_lin * (s_all[t] - s_small_over_q)
        axlx_sq = (q1_re + ax_rest + lx) ** 2 + q1_im ** 2
        if (t & 1) == 0:
            sum_sq_pos_even += axlx_sq
        else:
            sum_sq_pos_odd += axlx_sq

    # `δ_weightSplit = 1` in Lean, so both prefactors are `2`.
    card_even = 2 * (n_max // 2)
    card_odd = 2 * ((n_max + 1) // 2)
    rx_sq = (RX_CONST / float(x)) ** 2
    kernel_even = 2.0 * (2.0 * sum_sq_pos_even) + 2.0 * card_even * rx_sq
    kernel_odd = 2.0 * (2.0 * sum_sq_pos_odd) + 2.0 * card_odd * rx_sq
    return kernel_even, kernel_odd


def candidate_typei_u(x: int) -> float:
    masses = window_masses(x)
    weight0 = 1.0 - exact_major_zero_mode(x)
    window_upper = 0.0
    for n, diag in zip(masses.even_ns, masses.diag_mass_even):
        q0norm = (1.0 / 800.0) / (math.log(n) ** 2)
        window_upper += (q0norm * q0norm) * (weight0 * weight0) * diag
    norm_factor_sq = ((1.0 / 800.0) / (math.log(x + H) ** 2)) ** 2
    return window_upper / (norm_factor_sq * (1.0 / (H * (Q0**2))))


def candidate_ssu_u(x: int) -> float:
    masses = window_masses(x)
    kernel_even, kernel_odd = route_a_kernel_masses(x)
    weight0 = exact_major_zero_mode(x)
    window_upper = 0.0
    # For `X >= X0`, the window support is far from `n = 2`, so `aTerm2Mass = 0`.
    aterm2_mass = 0.0
    coeff_mass = masses.coeff_mass
    for n, diag in zip(masses.even_ns, masses.diag_mass_even):
        q0norm = (1.0 / 800.0) / (math.log(n) ** 2)
        pointwise = (q0norm * q0norm) * (
            2.0
            * (
                (2.0 * kernel_even) * (coeff_mass**2)
                + (4.0 * kernel_odd) * aterm2_mass * coeff_mass
                + (3.0 * (weight0**2)) * diag
            )
        )
        window_upper += pointwise
    norm_factor_sq = ((1.0 / 800.0) / (math.log(x + H) ** 2)) ** 2
    return window_upper / (norm_factor_sq * (H / float(x)))
