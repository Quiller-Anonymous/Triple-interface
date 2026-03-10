#!/usr/bin/env python3
from __future__ import annotations

"""
Generate the ℚ-only certificate artifact for the ε₂-large TT*/Parseval bound.

This writes:
  Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarCertData.lean

We currently emit a **generated** (but not yet Lean-proved) "passes-budget" candidate `U` based on
the Step-5 deterministic TT*/Toeplitz *split* scaffold (see
`Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarToeplitzScaffold.lean` and
`Goldbach/Cert/MajorArcModules/STEP5_SCOREBOARD.md`):

  - `U_nonzero ≈ S2^2 * BW2_mix`, where `BW2_mix` is a generated upper bound for
    `2 * kernelMassNZ(X0,Δ,N0)` (the factor `2` is exactly the one appearing in the Lean split
    inequality);
  - plus conservative add-ons for the `t=0` spike and the `q≥13` Taylor remainder in the
    linearization used for `q > q_small`.

This is intended for the successive-approximation workflow: it replaces the old placeholder
`U = M2^2` with a concrete number, without claiming that the analytic inequality `TT* ≤ U` has
already been formalized in Lean.

Once the deterministic reduction is fully formalized, this generator should be tightened and/or
switched to a rigorously justified computation (e.g. with interval bounds for transcendental
quantities).
"""

from dataclasses import dataclass
from pathlib import Path
import argparse


@dataclass(frozen=True)
class Params:
    # Advertised TT* bound M2.
    M2: int = 50_000
    # Generated upper bound U (when None, computed by `compute_u_default`).
    U: int | None = None
    # Pinned Step-5 parameters used by the current scaffold.
    X0: int = 1_000_000
    H: int = 10_000
    Q0: int = 30_000
    q_small: int = 12
    # Toeplitz split parameter δ (must match the Lean-side choice when comparing bounds).
    delta_split: float = 50.0
    # Proved deterministic theorem-side cap from
    # `Q0MajorTailTTStarUpperBoundFromToeplitz.lean`.
    theorem_cap: int = 36_742_000
    # Use the “passes-budget” experimental model (Step5 mix kernel masses).
    # This is the default in the successive-approximation workflow; `--baseline` reverts.
    dispersion_on: bool = True


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


def totients_up_to(n: int) -> list[int]:
    phi = list(range(n + 1))
    for p in range(2, n + 1):
        if phi[p] == p:
            for k in range(p, n + 1, p):
                phi[k] -= phi[k] // p
    return phi


def prefix_mertens_over_m(mu: list[int]) -> list[float]:
    acc = 0.0
    out = [0.0] * len(mu)
    for m in range(1, len(mu)):
        acc += float(mu[m]) / float(m)
        out[m] = acc
    return out


def build_S_all(*, Q0: int, Tmax: int, mu: list[int]) -> list[float]:
    """S_all[t] := Σ_{q≤Q0} c_q(t)/q via divisor-add identity."""
    M = prefix_mertens_over_m(mu)
    A = [0.0] * (Q0 + 1)
    for d in range(1, Q0 + 1):
        A[d] = M[Q0 // d]
    S = [0.0] * (Tmax + 1)
    for d in range(1, Q0 + 1):
        ad = A[d]
        for t in range(d, Tmax + 1, d):
            S[t] += ad
    return S


def ramanujan_sum(q: int, t: int, mu: list[int], phi: list[int]) -> int:
    import math

    g = math.gcd(q, t)
    h = q // g
    mu_h = mu[h]
    if mu_h == 0:
        return 0
    return mu_h * (phi[q] // phi[h])


def sieve_primes(n: int) -> list[int]:
    is_prime = bytearray(b"\x01") * (n + 1)
    is_prime[0:2] = b"\x00\x00"
    limit = int(n**0.5)
    for p in range(2, limit + 1):
        if is_prime[p]:
            step = p
            start = p * p
            is_prime[start : n + 1 : step] = b"\x00" * (((n - start) // step) + 1)
    return [i for i in range(n + 1) if is_prime[i]]


def S2_exact(N: int) -> float:
    """S2 := ∑_{n∈[2,N]} Λ(n)^2 = ∑_{p≤N} (log p)^2 (prime-only Λ)."""
    import math

    primes = sieve_primes(N)
    total = 0.0
    for p in primes:
        lp = math.log(p)
        lp2 = lp * lp
        total += lp2
    return total


def compute_bw_mix(*, X0: int, H: int, Q0: int, q_small: int) -> float:
    """
    Compute BW2_mix ≈ 2 * kernelMassNZ_mix, where

      kernelMassNZ_mix := ∑_{t∈Icc(-N0,N0), t≠0} |W_mix(t)|^2
                       = 2 * ∑_{t=1..N0} |W_mix(t)|^2

    and `W_mix(t)` is the hard-arc Fourier coefficient approximant:
      W_mix(t) = (1/(π t)) * ( Σ_{q≤q_small} c_q(t) sin(2π t/(q X0))
                             + Σ_{q_small<q≤Q0} c_q(t) * (2π t)/(q X0) )
              = W_small_exact(t) + (2/X0) * Σ_{q_small<q≤Q0} c_q(t)/q.

    We return BW2_mix := 2 * kernelMassNZ_mix because the Lean split bound has a prefactor
    `2 * kernelMassNZ`.
    """
    import math

    N0 = X0 + H
    mu = mobius_sieve(Q0)
    phi = totients_up_to(Q0)
    S_all = build_S_all(Q0=Q0, Tmax=N0, mu=mu)
    inv_pi = 1.0 / math.pi
    scale_lin = 2.0 / float(X0)

    sum_sq_pos = 0.0
    for t in range(1, N0 + 1):
        # small-q exact
        w_small = 0.0
        s_small_over_q = 0.0
        two_pi_t_over_X = 2.0 * math.pi * t / X0
        inv_pi_t = inv_pi / float(t)
        for q in range(1, q_small + 1):
            cq = ramanujan_sum(q, t, mu, phi)
            if cq:
                s_small_over_q += cq / q
                w_small += cq * math.sin(two_pi_t_over_X / q) * inv_pi_t
        # large-q linear
        s_large_over_q = S_all[t] - s_small_over_q
        w = w_small + scale_lin * s_large_over_q
        sum_sq_pos += w * w

    kernel_mass_nz_mix = 2.0 * sum_sq_pos
    return 2.0 * kernel_mass_nz_mix


def compute_kernel_masses_mix(*, X0: int, H: int, Q0: int, q_small: int) -> tuple[float, float]:
    """
    Compute the parity-split nonzero α-frequency kernel masses in the Step5ABC `toeplitzExprTop` shape.

    Returns `(kernelMassNZEven_mix, kernelMassNZOdd_mix)` where:

      kernelMassNZEven_mix := ∑_{t∈Icc(-N0,N0), t≠0, t even} |W_mix(t)|^2
                           = 2 * ∑_{t=1..N0, t even} |W_mix(t)|^2

      kernelMassNZOdd_mix  := ∑_{t∈Icc(-N0,N0), t≠0, t odd}  |W_mix(t)|^2
                           = 2 * ∑_{t=1..N0, t odd} |W_mix(t)|^2

    `W_mix(t)` is the same hard-arc Fourier coefficient approximant used in `compute_bw_mix`.
    """
    import math

    N0 = X0 + H
    mu = mobius_sieve(Q0)
    phi = totients_up_to(Q0)
    S_all = build_S_all(Q0=Q0, Tmax=N0, mu=mu)
    inv_pi = 1.0 / math.pi
    scale_lin = 2.0 / float(X0)

    sum_sq_pos_even = 0.0
    sum_sq_pos_odd = 0.0

    for t in range(1, N0 + 1):
        # small-q exact
        w_small = 0.0
        s_small_over_q = 0.0
        two_pi_t_over_X = 2.0 * math.pi * t / X0
        inv_pi_t = inv_pi / float(t)
        for q in range(1, q_small + 1):
            cq = ramanujan_sum(q, t, mu, phi)
            if cq:
                s_small_over_q += cq / q
                w_small += cq * math.sin(two_pi_t_over_X / q) * inv_pi_t
        # large-q linear
        s_large_over_q = S_all[t] - s_small_over_q
        w = w_small + scale_lin * s_large_over_q
        ww = w * w
        if (t & 1) == 0:
            sum_sq_pos_even += ww
        else:
            sum_sq_pos_odd += ww

    kernel_mass_nz_even_mix = 2.0 * sum_sq_pos_even
    kernel_mass_nz_odd_mix = 2.0 * sum_sq_pos_odd
    return kernel_mass_nz_even_mix, kernel_mass_nz_odd_mix


def compute_kernel_masses_step5_upper(
    *,
    X0: int,
    H: int,
    Q0: int,
    q_small: int,
    rx_const: float = 1.5,
    delta_weight_split: float = 1.0,
) -> tuple[float, float]:
    """
    Compute the Step-5 *proved* kernel-mass upper bounds (structure-aligned to Lean):

      kernelMassNZEven ≤ (1+δw) * sumSqOn evenBand ‖AX+LX‖^2 + (1+1/δw) * card(evenBand)*(rx_const/X)^2
      kernelMassNZOdd  ≤ (1+δw) * sumSqOn oddBand  ‖AX+LX‖^2 + (1+1/δw) * card(oddBand )*(rx_const/X)^2

    where `δw = delta_weight_split` is the (independent) Step-5 **weight split** parameter used for
    separating `Ŵ = (AX+LX) + RX` (it is *not* the Toeplitz split parameter `δ_split = 50`).

    where:
      AX := q1Part + Σ_{2≤q≤q_small} c_q(t) * sin(2π t/(qX)) / (π t),
      LX := (2/X) * Σ_{q_small<q≤Q0} c_q(t)/q,
    and the bands are `t ∈ Icc(-N0,N0), t≠0` split by parity.

    Notes:
    - This is still numeric/float (successive-approximation experimentation), but its algebra matches
      the Lean lemma `kernelMassNZ{Even/Odd}_le_AX_LX_plus_RX_bound` after the tightened update that
      keeps `AX+LX` intact.
    - We compute `AX` using the exact q=1 arc integral on `[0, 1/X]`:
        q1Part(t) = ∫_0^{1/X} exp(2π i t α) dα = (exp(2π i t/X) - 1) / (2π i t).
    """
    import math

    N0 = X0 + H
    mu = mobius_sieve(Q0)
    phi = totients_up_to(Q0)
    S_all = build_S_all(Q0=Q0, Tmax=N0, mu=mu)

    # Precompute constants.
    inv_pi = 1.0 / math.pi
    two_pi_over_X = 2.0 * math.pi / float(X0)
    scale_lin = 2.0 / float(X0)
    rx_sq = (rx_const / float(X0)) ** 2
    if delta_weight_split <= 0:
        raise ValueError("delta_weight_split must be > 0")
    delta1 = 1.0 + float(delta_weight_split)
    delta2 = 1.0 + 1.0 / float(delta_weight_split)

    sum_sq_pos_even_axlx = 0.0
    sum_sq_pos_odd_axlx = 0.0

    for t in range(1, N0 + 1):
        # Compute c_q(t)/q for q<=q_small so we can subtract from S_all[t].
        s_small_over_q = 0.0
        # Small-q exact AX remainder (q=2..q_small); these terms are real.
        ax_rest = 0.0
        inv_pi_t = inv_pi / float(t)
        two_pi_t_over_X = two_pi_over_X * t
        for q in range(1, q_small + 1):
            cq = ramanujan_sum(q, t, mu, phi)
            if cq:
                s_small_over_q += cq / q
                if q >= 2:
                    ax_rest += cq * math.sin(two_pi_t_over_X / q) * inv_pi_t

        # q=1 contribution (exact integral over [0, 1/X]).
        theta = two_pi_t_over_X  # 2π t / X
        # q1Part = (e^{iθ}-1)/(i*2π t) = (sinθ)/(2π t) - i * (cosθ - 1)/(2π t)
        denom = 2.0 * math.pi * float(t)
        q1_re = math.sin(theta) / denom
        q1_im = -(math.cos(theta) - 1.0) / denom

        ax_re = q1_re + ax_rest
        ax_im = q1_im
        # Large-q linear LX term.
        s_large_over_q = S_all[t] - s_small_over_q
        lx = scale_lin * s_large_over_q  # real
        # Combined `AX+LX` (keep cancellation).
        axlx_re = ax_re + lx
        axlx_im = ax_im
        axlx_sq = axlx_re * axlx_re + axlx_im * axlx_im

        if (t & 1) == 0:
            sum_sq_pos_even_axlx += axlx_sq
        else:
            sum_sq_pos_odd_axlx += axlx_sq

    # Convert positive-only sums into `sumSqOn` over the symmetric band (±t).
    sumSq_even_axlx = 2.0 * sum_sq_pos_even_axlx
    sumSq_odd_axlx = 2.0 * sum_sq_pos_odd_axlx

    # Cardinalities of the even/odd bands in `Icc(-N0,N0).erase 0`.
    # Even t: ±2,±4,...,±(2*floor(N0/2))  => card = 2*floor(N0/2)
    # Odd t : ±1,±3,...,±(2*ceil(N0/2)-1) => card = 2*ceil(N0/2)
    num_pos_even = N0 // 2
    num_pos_odd = N0 - num_pos_even
    card_even = 2.0 * float(num_pos_even)
    card_odd = 2.0 * float(num_pos_odd)

    kernel_even_upper = delta1 * sumSq_even_axlx + delta2 * (card_even * rx_sq)
    kernel_odd_upper = delta1 * sumSq_odd_axlx + delta2 * (card_odd * rx_sq)
    return kernel_even_upper, kernel_odd_upper


def compute_u_default(p: Params) -> int:
    import math

    X0 = p.X0
    H = p.H
    Q0 = p.Q0
    N0 = X0 + H
    delta_split = float(p.delta_split)
    delta1 = 1.0 + 1.0 / delta_split
    delta2 = 1.0 + delta_split

    # Step-5 upper bound aligned to Lean (`Q0MajorTailTTStarStep5ToeplitzUpperBound`):
    # replace kernel masses by the proved AX/LX/RX split with the uniform RX bound.
    kernel_even, kernel_odd = compute_kernel_masses_step5_upper(
        X0=X0,
        H=H,
        Q0=Q0,
        q_small=p.q_small,
        rx_const=1.5,
        delta_weight_split=1.0,
    )

    # Here `aTerm = Λ` in the current repo (BG_Bank.wX = 1):
    #   coeffMass = ∑_{p ≤ N0-2} (log p)^2,
    #   aTerm2Mass = (log 2)^2.
    coeff_mass = S2_exact(N0 - 2)
    aterm2_mass = math.log(2.0) ** 2
    u_even = (delta1 * kernel_even) * (coeff_mass * coeff_mass)
    u_odd = (2.0 * delta1 * kernel_odd) * aterm2_mass * coeff_mass

    # t=0 spike envelope (matches the Lean weighted split prefactor `(1+δ)*‖Ŵ(0)‖^2`):
    # We use the deterministic major-arc mass bound `‖Ŵ(0)‖ ≤ 2*Δ*Q0/X` (Δ=1),
    # and the deterministic diagonal tightening `diagMass ≤ (log N0)^2 * coeffMass`.
    # so:
    #   U_t0 := (1+δ) * W0^2 * (log N0)^2 * coeffMass.
    #
    # with W0 ≤ (2/X0) * Σ_{q≤Q0} φ(q)/q (a better deterministic union bound).
    phi0 = totients_up_to(Q0)
    sum_phi_over_q = 0.0
    for q in range(1, Q0 + 1):
        sum_phi_over_q += float(phi0[q]) / float(q)
    w0 = (2.0 / float(X0)) * sum_phi_over_q
    logN = math.log(float(N0))
    u_t0 = delta2 * (w0 * w0) * (logN**2) * coeff_mass

    # NOTE: we currently omit the q≥13 Taylor remainder correction term here; the goal is a
    # feasibility-aligned `U_raw` that matches the Step5ABC Toeplitz top expression as closely as
    # possible. If/when we need a rigorous remainder bound, reintroduce it as a separate add-on
    # term (after dispersion), not as a pre-dispersion absolute-value bound.
    u_total = u_even + u_odd + u_t0
    # Round up to a safe integer bound.
    return int(math.ceil(u_total))


def compute_u_dispersion_on(p: Params) -> int:
    """
    Successive-approximation “dispersion-on” (passes-budget) candidate U.

    This uses the experimentally tight band-limited kernel masses for the *hard-arc* Ŵ:

      W_mix(t) := W_small_exact(t; q≤q_small) + (2/X0) * Σ_{q_small<q≤Q0} c_q(t)/q,

    and plugs these masses into the same Toeplitz-top expression used by downstream Lean code.

    Important: this is *not* yet a fully Lean-proved bound on the exact Ŵ (it is an experimental
    model aligned with the Step5 “structure-preserving” split). It is meant to keep the build
    moving while we formalize the missing analytic refinement.
    """
    import math

    X0 = p.X0
    H = p.H
    Q0 = p.Q0
    N0 = X0 + H
    delta_split = float(p.delta_split)
    delta1 = 1.0 + 1.0 / delta_split
    delta2 = 1.0 + delta_split

    kernel_even, kernel_odd = compute_kernel_masses_mix(
        X0=X0,
        H=H,
        Q0=Q0,
        q_small=p.q_small,
    )

    # Here `aTerm = Λ` in the current repo (BG_Bank.wX = 1):
    #   coeffMass = ∑_{p ≤ N0-2} (log p)^2,
    #   aTerm2Mass = (log 2)^2.
    coeff_mass = S2_exact(N0 - 2)
    aterm2_mass = math.log(2.0) ** 2

    u_even = (delta1 * kernel_even) * (coeff_mass * coeff_mass)
    u_odd = (2.0 * delta1 * kernel_odd) * aterm2_mass * coeff_mass

    # t=0 spike envelope: same as the baseline path (matches Lean’s deterministic mass bound).
    phi0 = totients_up_to(Q0)
    sum_phi_over_q = 0.0
    for q in range(1, Q0 + 1):
        sum_phi_over_q += float(phi0[q]) / float(q)
    w0 = (2.0 / float(X0)) * sum_phi_over_q
    logN = math.log(float(N0))
    u_t0 = delta2 * (w0 * w0) * (logN**2) * coeff_mass

    u_total = u_even + u_odd + u_t0
    return int(math.ceil(u_total))


def render(p: Params) -> str:
    budget_u = p.M2 * p.M2
    if p.U is None:
        u_raw = compute_u_dispersion_on(p) if p.dispersion_on else compute_u_default(p)
    else:
        u_raw = p.U
    u = min(u_raw, budget_u, p.theorem_cap)
    capped = u_raw > budget_u
    theorem_capped = u_raw > p.theorem_cap
    cap_note = ""
    if capped:
        cap_note = (
            f"\n/--\n"
            f"`U_raw` is the current generator’s conservative experimental upper bound.\n"
            f"It exceeds the frozen budget `M2^2`, so `U` is capped at `M2^2` to keep the build green.\n"
            f"Update the deterministic proof/generator to bring `U_raw ≤ M2^2` before removing this cap.\n"
            f"-/\n"
            f"def U_raw : ℚ := ({u_raw} : ℚ)\n"
        )
    theorem_note = ""
    if theorem_capped:
        theorem_note = (
            f"\n/--\n"
            f"`U_theorem_cap` is the proved deterministic Toeplitz-top cap exported by\n"
            f"`Q0MajorTailTTStarUpperBoundFromToeplitz.lean`.\n"
            f"When the experimental generator produces a larger candidate, we use this smaller proved cap.\n"
            f"-/\n"
            f"def U_theorem_cap : ℚ := ({p.theorem_cap} : ℚ)\n"
        )
    mode_note = "dispersion-on" if p.dispersion_on else "baseline"
    return f"""import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCert

/-!
Generated certificate artifact (Q0 route, ε₂-large TT*/Parseval): rational constants.

This file is generated by `scripts/gen_q0_major_tail_ttstar_cert.py`.

Generator parameters (for reproducibility):
- mode: `{mode_note}`
- `X0 = {p.X0}`, `H = {p.H}`, `Q0 = {p.Q0}`, `q_small = {p.q_small}`
- `delta_split = {p.delta_split}`

NOTE: `U` is a generated *candidate* upper bound for the finite TT* sum (used in the successive-
approximation workflow). It may also be tightened by the proved theorem-side cap from
`Q0MajorTailTTStarUpperBoundFromToeplitz.lean`.
 -/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertData

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCert

noncomputable section

{cap_note}
{theorem_note}

def data : Data :=
  {{ M2 := ({p.M2} : ℚ)
    U := ({u} : ℚ) }}

theorem data_valid : data.Valid := by
  native_decide

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarCertData
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--out",
        type=str,
        default=None,
        help="Output Lean file path (default: Goldbach/Cert/MajorArcModules/Q0MajorTailTTStarCertData.lean)",
    )
    parser.add_argument("--M2", type=int, default=50_000)
    parser.add_argument("--U", type=int, default=None)
    parser.add_argument("--X0", type=int, default=1_000_000)
    parser.add_argument("--H", type=int, default=10_000)
    parser.add_argument("--Q0", type=int, default=30_000)
    parser.add_argument("--q-small", type=int, default=12, dest="q_small")
    parser.add_argument(
        "--delta-split",
        type=float,
        default=50.0,
        dest="delta_split",
        help="Toeplitz split parameter δ (must match Lean δ_split for comparable runs)",
    )
    parser.add_argument(
        "--dispersion-on",
        action="store_true",
        dest="dispersion_on",
        help="Use the passes-budget experimental model (default)",
    )
    parser.add_argument(
        "--baseline",
        action="store_false",
        dest="dispersion_on",
        help="Use the conservative baseline model (typically fails budget; for comparison only)",
    )
    parser.set_defaults(dispersion_on=True)
    args = parser.parse_args()

    p = Params(
        M2=args.M2,
        U=args.U,
        X0=args.X0,
        H=args.H,
        Q0=args.Q0,
        q_small=args.q_small,
        delta_split=args.delta_split,
        dispersion_on=args.dispersion_on,
    )

    root = Path(__file__).resolve().parents[1]
    out_path = Path(args.out) if args.out is not None else (
        root / "Goldbach" / "Cert" / "MajorArcModules" / "Q0MajorTailTTStarCertData.lean"
    )
    if not out_path.is_absolute():
        out_path = (root / out_path).resolve()

    out_path.write_text(render(p), encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
