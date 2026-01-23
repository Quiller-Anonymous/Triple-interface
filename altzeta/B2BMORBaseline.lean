import AltZeta.B2Comparator
import AltZeta.B2RealBound
import Goldbach.Cert.ExplicitPNTinAP_BMOR
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
AltZeta/B2BMORBaseline.lean
===========================

An unconditional “ζ-style” baseline envelope on the canonical window, sourced from the
Bennett–Martin–O’Bryant–Rechnitzer (BMOR) explicit `ψ` bound constants.

This file does **not** claim that BMOR bounds our smoothed `Ψ_K` statistic; it only records:

* the canonical real-valued baseline envelope `Eζ(x) := Cψ · x / log x`, and
* the (easy) inequality that our canonical B2 envelope `ETrunc0(x) = 1/4 + √x/10` is strictly
  smaller than that baseline on the canonical dyadic window `x ∈ [10^6, 2·10^6]`.

This is a first “diagnostic” step toward a fair outpowering comparison, once a genuine ζ-only
bound package for the same smoothed statistic is wired in.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real
open Nat
open Goldbach.Cert.ExplicitPNTinAP_BMOR

/-- BMOR-style baseline envelope on the canonical window: `Eζ(x) := Cψ · x / log x`. -/
def baselineBMOR0 : ZetaBaseline W0 :=
{ EZeta := fun x => Cψ * x / Real.log x
, EZeta_nonneg := by
    intro x hx
    have hx_lower : (10 ^ 6 : ℝ) ≤ x := by
      simpa [W0, canonicalWindow, B2.canonicalWindow, Goldbach.ETIExport.canonicalWindow] using hx.1
    have hx_gt_one : (1 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (1 : ℝ) < (10 ^ 6 : ℝ)) hx_lower
    have hx_pos : 0 < x := hx.2.2
    have hlog_pos : 0 < Real.log x := Real.log_pos hx_gt_one
    have hnum_nonneg : 0 ≤ Cψ * x := mul_nonneg Cψ_nonneg hx_pos.le
    exact div_nonneg hnum_nonneg hlog_pos.le
}

namespace baselineBMOR0

lemma EZeta_def (x : ℝ) : (baselineBMOR0).EZeta x = Cψ * x / Real.log x := rfl

end baselineBMOR0

/-! ### A crude but explicit log upper bound on the canonical window -/

lemma twoX0_le_exp_twenty : (2 * (10 ^ 6 : ℝ)) ≤ Real.exp 20 := by
  -- `exp 20` dominates the 10-term partial sum `∑_{i<10} 20^i/i!`, which already exceeds `2·10^6`.
  have hsum_le : (∑ i ∈ Finset.range 10, (20 : ℝ) ^ i / i !) ≤ Real.exp 20 :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 20) 10
  have htwo_le : (2 * (10 ^ 6 : ℝ)) ≤ (20 : ℝ) ^ 8 / 8 ! + (20 : ℝ) ^ 9 / 9 ! := by
    norm_num
  have hsubset :
      (∑ i ∈ ({8, 9} : Finset ℕ), (20 : ℝ) ^ i / i !) ≤
        ∑ i ∈ Finset.range 10, (20 : ℝ) ^ i / i ! := by
    have hsub : ({8, 9} : Finset ℕ) ⊆ Finset.range 10 := by
      intro i hi
      have hi' : i = 8 ∨ i = 9 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hi
      have : i < 10 := by
        rcases hi' with rfl | rfl <;> decide
      exact (Finset.mem_range).2 this
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _hi _hnot
    positivity
  have htwo_le_subset :
      (2 * (10 ^ 6 : ℝ)) ≤ ∑ i ∈ ({8, 9} : Finset ℕ), (20 : ℝ) ^ i / i ! := by
    -- unfold the two-term sum
    simpa using htwo_le
  exact le_trans (le_trans htwo_le_subset hsubset) hsum_le

lemma log_le_twenty_of_validX0 {x : ℝ} (hx : ValidX W0 x) : Real.log x ≤ 20 := by
  have hx_pos : 0 < x := hx.2.2
  have hx_le : x ≤ 2 * W0.X := hx.2.1
  have hX0 : W0.X = (10 ^ 6 : ℝ) := by
    simp [W0, canonicalWindow, B2.canonicalWindow, Goldbach.ETIExport.canonicalWindow]
  have hx_le' : x ≤ 2 * (10 ^ 6 : ℝ) := by simpa [hX0] using hx_le
  have hx_le_exp : x ≤ Real.exp 20 := le_trans hx_le' twoX0_le_exp_twenty
  have hlog_le : Real.log x ≤ Real.log (Real.exp 20) := Real.log_le_log hx_pos hx_le_exp
  simpa using (hlog_le.trans_eq (by simp))

/-! ### Envelope comparison: `ETrunc0 < Eζ_BMOR` on the canonical window -/

lemma ETrunc0_lt_Cψ_mul_div_twenty {x : ℝ} (hx : ValidX W0 x) :
    ETrunc0 x < Cψ * (x / 20) := by
  have hx_lower : (10 ^ 6 : ℝ) ≤ x := by
    simpa [W0, canonicalWindow, B2.canonicalWindow, Goldbach.ETIExport.canonicalWindow] using hx.1
  have hx_pos : 0 < x := hx.2.2
  have hsqrt_le : Real.sqrt x ≤ x / 1000 := by
    have h1000_le : (1000 : ℝ) ≤ Real.sqrt x := by
      -- `x ≥ 10^6 = 1000^2`
      have hsq : (1000 : ℝ) ^ 2 ≤ x := by
        -- `1000^2 = 10^6`
        have : (1000 : ℝ) ^ 2 = (10 ^ 6 : ℝ) := by norm_num
        simpa [this] using hx_lower
      exact (Real.le_sqrt_of_sq_le hsq)
    have hx_nonneg : 0 ≤ x := hx_pos.le
    have hmul : (1000 : ℝ) * Real.sqrt x ≤ x := by
      calc
        (1000 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (mul_le_mul_of_nonneg_right h1000_le (Real.sqrt_nonneg x))
        _ = x := by simpa [Real.mul_self_sqrt hx_nonneg]
    -- divide by `1000`
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hsqrt_term :
      Real.sqrt x * S0 ≤ x / 10000 := by
    -- `S0 = 1/10` and `√x ≤ x/1000`
    have hS0 : S0 = (1 : ℝ) / 10 := by
      simp [S0, Goldbach.Census.S_cert, Goldbach.Census.S_cert_value]
    have hsqrt_div10 : Real.sqrt x / 10 ≤ x / 10000 := by
      have h' : Real.sqrt x / 10 ≤ (x / 1000) / 10 :=
        div_le_div_of_nonneg_right hsqrt_le (by norm_num : (0 : ℝ) ≤ 10)
      -- simplify the RHS: `(x/1000)/10 = x/10000`
      have : (x / 1000 : ℝ) / 10 = x / 10000 := by
        -- `a/b/c = a/(b*c)` and `10*1000 = 10000`
        have h : (10 : ℝ) * 1000 = 10000 := by norm_num
        -- `simp` decides the rearrangement; `h` closes the numeral arithmetic.
        simp [div_div, h, mul_assoc, mul_comm, mul_left_comm]
      exact (h'.trans_eq this)
    -- rewrite `S0` into `1/10` and use `hsqrt_div10`
    simpa [hS0, div_eq_mul_inv, mul_assoc] using hsqrt_div10
  have hCGamma0 : CGamma0 = (1 : ℝ) / 4 := by
    simp [CGamma0, Goldbach.Census.CGamma, Goldbach.Census.CGamma_value]
  have hbound :
      ETrunc0 x ≤ (1 : ℝ) / 4 + x / 10000 := by
    calc
      ETrunc0 x = CGamma0 + Real.sqrt x * S0 := by rfl
      _ ≤ CGamma0 + x / 10000 := add_le_add_left hsqrt_term _
      _ = (1 : ℝ) / 4 + x / 10000 := by simp [hCGamma0]
  have hstrict : (1 : ℝ) / 4 + x / 10000 < Cψ * (x / 20) := by
    -- This is an elementary inequality once `x ≥ 10^6`.
    -- `Cψ = 11/1000`.
    have hCψ : Cψ = (11 : ℝ) / 1000 := by simp [Cψ]
    nlinarith [hx_lower, hCψ]
  exact lt_of_le_of_lt hbound hstrict

/-- Our canonical B2 envelope beats the BMOR-style baseline on the whole canonical window. -/
theorem ETrunc0_lt_baselineBMOR0 {x : ℝ} (hx : ValidX W0 x) :
    ETrunc0 x < (baselineBMOR0).EZeta x := by
  have hx_pos : 0 < x := hx.2.2
  have hx_nonneg : 0 ≤ x := hx_pos.le
  have hx_lower : (10 ^ 6 : ℝ) ≤ x := by
    simpa [W0, canonicalWindow, B2.canonicalWindow, Goldbach.ETIExport.canonicalWindow] using hx.1
  have hx_gt_one : (1 : ℝ) < x :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < (10 ^ 6 : ℝ)) hx_lower
  have hlog_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hlog_le : Real.log x ≤ 20 := log_le_twenty_of_validX0 hx
  have hdiv :
      x / 20 ≤ x / Real.log x :=
    div_le_div_of_nonneg_left hx_nonneg hlog_pos hlog_le
  have hCψ_nonneg : 0 ≤ Cψ := Cψ_nonneg
  have hbaseline_lower : Cψ * (x / 20) ≤ Cψ * (x / Real.log x) :=
    mul_le_mul_of_nonneg_left hdiv hCψ_nonneg
  have hE : ETrunc0 x < Cψ * (x / 20) := ETrunc0_lt_Cψ_mul_div_twenty (x := x) hx
  -- `baselineBMOR0.EZeta x = Cψ * x / log x`.
  have : Cψ * (x / Real.log x) = (baselineBMOR0).EZeta x := by
    -- rewrite `Cψ * (x / log x)` into `(Cψ * x) / log x`
    simpa [baselineBMOR0, ZetaBaseline, mul_div_assoc, mul_assoc]
  exact lt_of_lt_of_le hE (hbaseline_lower.trans_eq this)

/-- Canonical B2 bound implies a certified “beats baseline” pointwise comparison (envelopes). -/
theorem beatsBaselineBMOR0 {x : ℝ} (hx : ValidX W0 x) :
    BeatsBaselineAt trunc0 tail0 baselineBMOR0 x := by
  -- `EFull(trunc0,tail0)=ETrunc0` for the canonical hat kernel.
  have hEFull : EFull trunc0 tail0 x = ETrunc0 x := EFull0_eq_ETrunc0 (x := x)
  have hlt : ETrunc0 x < (baselineBMOR0).EZeta x := ETrunc0_lt_baselineBMOR0 (x := x) hx
  simpa [BeatsBaselineAt, hEFull] using hlt

/-- The BMOR-style gain metric is strictly larger than `1` on the canonical window. -/
theorem gainBMOR0_gt_one {x : ℝ} (hx : ValidX W0 x) :
    1 < WindowErrorGain trunc0 tail0 baselineBMOR0 x := by
  have hpos : 0 < EFull trunc0 tail0 x := by
    -- `EFull = ETrunc0` and `ETrunc0` is strictly positive on valid windows.
    have hEFull : EFull trunc0 tail0 x = ETrunc0 x := EFull0_eq_ETrunc0 (x := x)
    have hxpos : 0 < ETrunc0 x := ETrunc0_pos x hx
    simpa [hEFull] using hxpos
  have hlt : EFull trunc0 tail0 x < (baselineBMOR0).EZeta x := by
    simpa [BeatsBaselineAt] using beatsBaselineBMOR0 (x := x) hx
  -- `gain = EZeta / EFull`, and `0 < EFull`.
  have : 1 < (baselineBMOR0).EZeta x / EFull trunc0 tail0 x :=
    (one_lt_div_iff).2 (Or.inl ⟨hpos, hlt⟩)
  simpa [WindowErrorGain] using this

end B2
end AltZeta
