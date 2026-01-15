import Goldbach.Cert.ExplicitPNTinAP_BMOR
import Goldbach.Cert.SiegelWalfiszWeighted
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.Cert.CanonLogBounds
import Mathlib.Data.Real.Basic

/-!
Consequences of the explicit PNT-in-AP ψ-bound (`ExplicitPNTinAP_BMOR.psi_bound`).

The goal of this file is to provide “drop-in” bounds on the SW deviation

`E(x) = ψ(x; q, a) - x/φ(q)`

in the forms that later major-arc bookkeeping typically consumes: a pointwise bound and a uniform
bound over an interval `x ∈ [X,U]`.

This file does **not** attempt to rerun the whole major-arc chain; it just exposes the algebraic
pieces needed to do so later (or to build a certificate/checker that uses the explicit constants).
-/

namespace Goldbach.Cert
namespace ExplicitPNTinAP_BMOR
namespace Consequences

open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.SiegelWalfiszWeighted
open Goldbach.AO_OffDiag.TailBlock
open Goldbach.Cert.CanonLogBounds

noncomputable section

variable (q a : ℕ)

lemma Q0_le_Qmax : (Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) ≤ Qmax := by
  -- `30000 ≤ 100000`
  norm_num [Goldbach.AO_OffDiag.TailBlock.Q0, Qmax]

private lemma log_pos_of_Xmin_le {X : ℕ} (hX : Xmin ≤ X) : 0 < Real.log (X : ℝ) := by
  have hX2 : (2 : ℕ) ≤ X := le_trans (by
      -- `2 ≤ 10^6`
      norm_num [Xmin]) hX
  have hX2' : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have h1X : (1 : ℝ) < (X : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hX2'
  exact Real.log_pos h1X

/-!
### Trivial `ψ`/`E` bounds below the BMOR cutoff

BMOR provides a strong bound only for `x ≥ Xmin`. For “certificate-first” bookkeeping it is
convenient to also have a uniform (but very weak) bound for `2 ≤ x ≤ Xmin`, derived purely from
elementary inequalities and the definition of `SiegelWalfisz.psi`.

These lemmas are *not* intended to be sharp; they exist to avoid low-end cutoffs showing up as
side-conditions in later files.
-/

private lemma log_pos_of_two_le {x : ℕ} (hx : 2 ≤ x) : 0 < Real.log (x : ℝ) := by
  have hx' : (1 : ℝ) < (x : ℝ) := by
    have hx'' : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hx''
  exact Real.log_pos hx'

private lemma psi_nonneg (x q a : ℕ) : 0 ≤ psi x q a := by
  classical
  -- Termwise nonnegativity: `ΛVM n ≥ 0`, so the conditional summand is nonnegative.
  unfold SiegelWalfisz.psi
  refine Finset.sum_nonneg ?_
  intro n hn
  by_cases h : Nat.ModEq q n a
  · have hΛ : 0 ≤ ΛVM n := by
      simpa [SiegelWalfisz.ΛVM] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    simpa [h] using hΛ
  · simp [h]

private lemma psi_le_sum_vonMangoldt (x q a : ℕ) :
    psi x q a ≤ Finset.sum (Finset.range (x + 1)) (fun n => ΛVM n) := by
  classical
  -- Drop the congruence filter using `0 ≤ ΛVM n`.
  unfold SiegelWalfisz.psi
  refine Finset.sum_le_sum ?_
  intro n hn
  by_cases h : Nat.ModEq q n a
  · simp [h]
  · have hΛ : 0 ≤ ΛVM n := by
      simpa [SiegelWalfisz.ΛVM] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    simpa [h] using hΛ

private lemma sum_vonMangoldt_le_sum_log (x : ℕ) :
    Finset.sum (Finset.range (x + 1)) (fun n => ΛVM n)
      ≤ Finset.sum (Finset.range (x + 1)) (fun n => Real.log (n : ℝ)) := by
  classical
  refine Finset.sum_le_sum ?_
  intro n hn
  -- `ΛVM n = (vonMangoldt n : ℝ) ≤ log n`.
  simpa [SiegelWalfisz.ΛVM] using (ArithmeticFunction.vonMangoldt_le_log (n := n))

private lemma sum_log_range_succ_le (x : ℕ) :
    Finset.sum (Finset.range (x + 1)) (fun n => Real.log (n : ℝ))
      ≤ (x : ℝ) * Real.log (x : ℝ) := by
  classical
  -- Peel off the `n = 0` term: `log 0 = 0`.
  have hrewrite :
      Finset.sum (Finset.range (x + 1)) (fun n => Real.log (n : ℝ))
        =
      Finset.sum (Finset.range x) (fun n => Real.log ((n + 1 : ℕ) : ℝ)) := by
    -- `sum_range_succ'` shifts the index and isolates the `n = 0` term.
    have :=
      (Finset.sum_range_succ' (fun n : ℕ => Real.log (n : ℝ)) x)
    -- The isolated `log 0` term vanishes.
    simpa using (by
      simpa [Real.log_zero, add_comm, add_left_comm, add_assoc] using this)
  -- Bound each term by `log x` (monotonicity of `log` on `n+1 ≤ x`).
  have hle :
      Finset.sum (Finset.range x) (fun n => Real.log ((n + 1 : ℕ) : ℝ))
        ≤
      Finset.sum (Finset.range x) (fun _n => Real.log (x : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have hnx : n < x := Finset.mem_range.mp hn
    have hle_nat : n + 1 ≤ x := Nat.succ_le_of_lt hnx
    have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos n)
    exact Real.log_le_log hpos (by exact_mod_cast hle_nat)
  -- Compute the constant sum.
  -- Compute the constant sum.
  have hconst :
      Finset.sum (Finset.range x) (fun _n => Real.log (x : ℝ)) = (x : ℝ) * Real.log (x : ℝ) := by
    simp [mul_comm, mul_left_comm, mul_assoc]
  -- Combine.
  calc
    Finset.sum (Finset.range (x + 1)) (fun n => Real.log (n : ℝ))
        =
      Finset.sum (Finset.range x) (fun n => Real.log ((n + 1 : ℕ) : ℝ)) := hrewrite
    _ ≤ Finset.sum (Finset.range x) (fun _n => Real.log (x : ℝ)) := hle
    _ = (x : ℝ) * Real.log (x : ℝ) := hconst

/--
Crude bound on the SW deviation `E(x)` for `2 ≤ x ≤ Xmin`.

This uses only:
- `|E| ≤ ψ + x/φ(q)` (triangle inequality),
- `ψ ≤ x log x` (via `Λ ≤ log` termwise),
- `x/φ(q) ≤ x` (since `φ(q) ≥ 1` for `q ≥ 1`),
and then rewrites the result in `x/log x` form with a fixed constant depending only on `Xmin`.
-/
theorem abs_E_le_trivial_on_Icc
    {x : ℕ} (hx2 : 2 ≤ x) (hx : x ≤ Xmin) (hq : 1 ≤ q) :
    |E (q := q) (a := a) x|
      ≤ ((Real.log (Xmin : ℝ) + 1) * Real.log (Xmin : ℝ)) * (x : ℝ) / Real.log (x : ℝ) := by
  have hlog_pos : 0 < Real.log (x : ℝ) := log_pos_of_two_le (x := x) hx2
  have hlog_ne : Real.log (x : ℝ) ≠ 0 := ne_of_gt hlog_pos

  have hψ_nonneg : 0 ≤ psi x q a := psi_nonneg x q a
  have hq_pos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hφ_pos : 0 < Nat.totient q := (Nat.totient_pos).2 hq_pos
  have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
    -- `1 ≤ φ(q)` since `0 < φ(q)`.
    have : (1 : ℕ) ≤ Nat.totient q := (Nat.succ_le_iff.2 hφ_pos)
    exact_mod_cast this
  have hx0 : 0 ≤ (x : ℝ) := by positivity
  have hmain_le : (x : ℝ) / (Nat.totient q : ℝ) ≤ (x : ℝ) := by
    simpa using (div_le_self hx0 hφ1)

  have hψ_le :
      psi x q a ≤ (x : ℝ) * Real.log (x : ℝ) := by
    have h1 : psi x q a ≤ Finset.sum (Finset.range (x + 1)) (fun n => ΛVM n) :=
      psi_le_sum_vonMangoldt x q a
    have h2 : Finset.sum (Finset.range (x + 1)) (fun n => ΛVM n)
        ≤ Finset.sum (Finset.range (x + 1)) (fun n => Real.log (n : ℝ)) :=
      sum_vonMangoldt_le_sum_log (x := x)
    have h3 : Finset.sum (Finset.range (x + 1)) (fun n => Real.log (n : ℝ))
        ≤ (x : ℝ) * Real.log (x : ℝ) :=
      sum_log_range_succ_le (x := x)
    exact le_trans h1 (le_trans h2 h3)

  -- Triangle inequality: `|ψ - x/φ| ≤ |ψ| + |x/φ| = ψ + x/φ`.
  have htri :
      |E (q := q) (a := a) x|
        ≤ psi x q a + (x : ℝ) / (Nat.totient q : ℝ) := by
    have hxφ_nonneg : 0 ≤ (x : ℝ) / (Nat.totient q : ℝ) := by
      exact div_nonneg hx0 (by exact_mod_cast (le_of_lt hφ_pos))
    -- `abs_add_le` is available in this toolchain snapshot.
    have h :=
      abs_add_le (psi x q a) (-( (x : ℝ) / (Nat.totient q : ℝ)))
    -- Rewrite the LHS and simplify absolute values using nonnegativity.
    have :
        |psi x q a - (x : ℝ) / (Nat.totient q : ℝ)|
          ≤ psi x q a + (x : ℝ) / (Nat.totient q : ℝ) := by
      simpa [sub_eq_add_neg, abs_neg, abs_of_nonneg hψ_nonneg, abs_of_nonneg hxφ_nonneg] using h
    simpa [SiegelWalfiszWeighted.E] using this

  have hE_le : |E (q := q) (a := a) x| ≤ (x : ℝ) * Real.log (x : ℝ) + (x : ℝ) := by
    have := le_trans htri (add_le_add hψ_le hmain_le)
    -- simplify `ψ + x/φ ≤ x log x + x`
    simpa [add_assoc, add_left_comm, add_comm] using this

  -- Rewrite `x log x + x` as `(log x + 1) * x`.
  have hrewrite1 :
      (x : ℝ) * Real.log (x : ℝ) + (x : ℝ) = (Real.log (x : ℝ) + 1) * (x : ℝ) := by
    ring

  have hrewrite2 :
      (Real.log (x : ℝ) + 1) * (x : ℝ)
        =
      ((Real.log (x : ℝ) + 1) * Real.log (x : ℝ)) * ((x : ℝ) / Real.log (x : ℝ)) := by
    -- Clear denominators (safe since `log x ≠ 0` for `x ≥ 2`).
    field_simp [hlog_ne]

  -- Bound `((log x + 1) * log x)` by the same expression at `Xmin`.
  have hlog_le : Real.log (x : ℝ) ≤ Real.log (Xmin : ℝ) := by
    have hxpos' : 0 < x := by
      have : 1 ≤ x := le_trans (by decide : (1 : ℕ) ≤ 2) hx2
      exact lt_of_lt_of_le Nat.zero_lt_one this
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast hxpos'
    have hx_le : (x : ℝ) ≤ (Xmin : ℝ) := by exact_mod_cast hx
    exact Real.log_le_log hxpos hx_le
  have hlog_nonneg : 0 ≤ Real.log (x : ℝ) := le_of_lt hlog_pos
  have hsq_le :
      (Real.log (x : ℝ)) ^ 2 ≤ (Real.log (Xmin : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlog_nonneg hlog_le 2
  have hpoly_le :
      (Real.log (x : ℝ)) ^ 2 + Real.log (x : ℝ)
        ≤
      (Real.log (Xmin : ℝ)) ^ 2 + Real.log (Xmin : ℝ) := by
    exact add_le_add hsq_le hlog_le
  have hfac_le :
      (Real.log (x : ℝ) + 1) * Real.log (x : ℝ)
        ≤
      (Real.log (Xmin : ℝ) + 1) * Real.log (Xmin : ℝ) := by
    -- `(t+1)t = t^2 + t`
    have ht : (Real.log (x : ℝ) + 1) * Real.log (x : ℝ) = (Real.log (x : ℝ)) ^ 2 + Real.log (x : ℝ) := by
      ring
    have hu :
        (Real.log (Xmin : ℝ) + 1) * Real.log (Xmin : ℝ)
          =
        (Real.log (Xmin : ℝ)) ^ 2 + Real.log (Xmin : ℝ) := by
      ring
    simpa [ht, hu] using hpoly_le

  have hratio_nonneg : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    exact div_nonneg hx0 (le_of_lt hlog_pos)

  -- Multiply the factor bound by the nonnegative ratio.
  have := mul_le_mul_of_nonneg_right hfac_le hratio_nonneg

  -- Finish by chaining.
  calc
    |E (q := q) (a := a) x|
        ≤ (Real.log (x : ℝ) + 1) * (x : ℝ) := by
            simpa [hrewrite1] using hE_le
    _ = ((Real.log (x : ℝ) + 1) * Real.log (x : ℝ)) * ((x : ℝ) / Real.log (x : ℝ)) := hrewrite2
    _ ≤ ((Real.log (Xmin : ℝ) + 1) * Real.log (Xmin : ℝ)) * ((x : ℝ) / Real.log (x : ℝ)) := by
            simpa [mul_assoc] using this
    _ = ((Real.log (Xmin : ℝ) + 1) * Real.log (Xmin : ℝ)) * (x : ℝ) / Real.log (x : ℝ) := by
            simp [div_eq_mul_inv, mul_assoc]

/-- Pointwise bound for the SW deviation `E(x)` from the explicit ψ(AP) estimate. -/
theorem abs_E_le_of_psi_bound
    {x : ℕ} (hx : Xmin ≤ x) (hq : 1 ≤ q) (hqQ : q ≤ Qmax) (hcop : Nat.Coprime a q) :
    |E (q := q) (a := a) x| ≤ Cψ * (x : ℝ) / Real.log (x : ℝ) := by
  -- `E x` is definitionally `psi x q a - x/φ(q)`.
  simpa [SiegelWalfiszWeighted.E] using (psi_bound (x := x) (q := q) (a := a) hx hq hqQ hcop)

/--
Uniform `E`-bound on an interval `x ∈ [X,U]`, in the “`U / log X`” form.

This uses only monotonicity of `log` on `x ≥ 2` and the trivial monotonicity `x ≤ U`.
-/
theorem abs_E_le_uniform_on_Icc
    {X U : ℕ} (hX : Xmin ≤ X)
    (hq : 1 ≤ q) (hqQ : q ≤ Qmax) (hcop : Nat.Coprime a q) :
    ∀ {x : ℕ}, x ∈ Finset.Icc X U →
      |E (q := q) (a := a) x| ≤ Cψ * (U : ℝ) / Real.log (X : ℝ) := by
  intro x hx
  have hxX : X ≤ x := (Finset.mem_Icc.mp hx).1
  have hxU : x ≤ U := (Finset.mem_Icc.mp hx).2
  have hx' : Xmin ≤ x := le_trans hX hxX

  have hlogX_pos : 0 < Real.log (X : ℝ) := log_pos_of_Xmin_le (X := X) hX
  have hlogx_pos : 0 < Real.log (x : ℝ) := log_pos_of_Xmin_le (X := x) hx'
  have hlog_mono : Real.log (X : ℝ) ≤ Real.log (x : ℝ) := by
    have hXpos : 0 < (X : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by
      -- `0 < 10^6`
      norm_num [Xmin]) hX)
    exact Real.log_le_log hXpos (by exact_mod_cast hxX)
  have hpow_inv :
      (Real.log (x : ℝ))⁻¹ ≤ (Real.log (X : ℝ))⁻¹ :=
    (inv_le_inv₀ hlogx_pos hlogX_pos).2 hlog_mono

  have hxU_real : (x : ℝ) ≤ (U : ℝ) := by exact_mod_cast hxU
  have hdiv :
      (x : ℝ) / Real.log (x : ℝ) ≤ (U : ℝ) / Real.log (X : ℝ) := by
    -- `x/log x = x * (log x)⁻¹ ≤ U * (log X)⁻¹`
    calc
      (x : ℝ) / Real.log (x : ℝ) = (x : ℝ) * (Real.log (x : ℝ))⁻¹ := by
        simp [div_eq_mul_inv]
      _ ≤ (U : ℝ) * (Real.log (x : ℝ))⁻¹ := by
        exact mul_le_mul_of_nonneg_right hxU_real (by positivity)
      _ ≤ (U : ℝ) * (Real.log (X : ℝ))⁻¹ := by
        exact mul_le_mul_of_nonneg_left hpow_inv (by positivity)
      _ = (U : ℝ) / Real.log (X : ℝ) := by simp [div_eq_mul_inv]

  have hEx := abs_E_le_of_psi_bound (q := q) (a := a) (x := x) hx' hq hqQ hcop
  have hC_nonneg : 0 ≤ Cψ := Cψ_nonneg
  have := mul_le_mul_of_nonneg_left hdiv hC_nonneg
  exact le_trans hEx (by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this)

/-! Convenience specialization: the project’s `Q0 = 30000` lies inside BMOR’s `Qmax = 100000`. -/

theorem abs_E_le_uniform_on_Icc_Q0
    {X U : ℕ} (hX : Xmin ≤ X)
    (hq : 1 ≤ q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0) (hcop : Nat.Coprime a q) :
    ∀ {x : ℕ}, x ∈ Finset.Icc X U →
      |E (q := q) (a := a) x| ≤ Cψ * (U : ℝ) / Real.log (X : ℝ) := by
  intro x hx
  have hqQ : q ≤ Qmax :=
    le_trans hqQ0 (Q0_le_Qmax : (Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) ≤ Qmax)
  exact abs_E_le_uniform_on_Icc (q := q) (a := a) (X := X) (U := U) hX hq hqQ hcop hx

/-!
### A single uniform bound (no `x ≥ Xmin` side condition)

For certificate-oriented bookkeeping it is useful to have a “one line” bound that applies for all
`x ≥ 2` (at the cost of a much weaker constant).  This matches the recommended `210 * x/log x`
envelope: it is strong enough to eliminate `Xmin` side-conditions in later reductions, while
keeping the statement simple and stable.
-/

private lemma Ctriv_le_210 :
    ((Real.log (Xmin : ℝ) + 1) * Real.log (Xmin : ℝ)) ≤ (210 : ℝ) := by
  -- `Xmin = X0 = 10^6`, so reuse the canonical `log` bound.
  simpa [Goldbach.BankParams.X0, Xmin, Goldbach.BankParams.X0] using
    (Goldbach.Cert.CanonLogBounds.log_X0_plus_one_mul_log_X0_le_210)

theorem abs_E_le_210_of_two_le
    {x : ℕ} (hx2 : 2 ≤ x) (hq : 1 ≤ q) (hqQ : q ≤ Qmax) (hcop : Nat.Coprime a q) :
    |E (q := q) (a := a) x| ≤ (210 : ℝ) * (x : ℝ) / Real.log (x : ℝ) := by
  have hlog_pos : 0 < Real.log (x : ℝ) := log_pos_of_two_le (x := x) hx2
  have hratio_nonneg : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    exact div_nonneg (by positivity) (le_of_lt hlog_pos)
  -- Split at `Xmin`.
  rcases le_total x Xmin with hx_le | hx_ge
  · -- Below the cutoff: use the trivial bound and cap the constant by `210`.
    have htriv :=
      abs_E_le_trivial_on_Icc (q := q) (a := a) (x := x) hx2 hx_le hq
    have hC : ((Real.log (Xmin : ℝ) + 1) * Real.log (Xmin : ℝ)) ≤ (210 : ℝ) := Ctriv_le_210
    have hC' :=
      mul_le_mul_of_nonneg_right hC hratio_nonneg
    -- Rewrite and chain.
    have : ((Real.log (Xmin : ℝ) + 1) * Real.log (Xmin : ℝ)) * (x : ℝ) / Real.log (x : ℝ)
        ≤ (210 : ℝ) * (x : ℝ) / Real.log (x : ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hC'
    exact le_trans htriv this
  · -- Above the cutoff: BMOR gives the sharper bound with `Cψ ≤ 210`.
    have hxX : Xmin ≤ x := hx_ge
    have hE :=
      abs_E_le_of_psi_bound (q := q) (a := a) (x := x) hxX hq hqQ hcop
    have hC : Cψ ≤ (210 : ℝ) := by
      -- `0.011 ≤ 210` (we keep it exact as a rational comparison).
      norm_num [Cψ]
    have hC' := mul_le_mul_of_nonneg_right hC hratio_nonneg
    have : Cψ * (x : ℝ) / Real.log (x : ℝ) ≤ (210 : ℝ) * (x : ℝ) / Real.log (x : ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hC'
    exact le_trans hE this

end

end Consequences
end ExplicitPNTinAP_BMOR
end Goldbach.Cert
