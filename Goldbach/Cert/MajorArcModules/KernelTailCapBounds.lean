import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Stable numeric bounds for the `Q0` large-β kernel tail cap.

This file exists so certificate artifacts can remain purely rational (`ℚ`), while the only
transcendental interaction (`Real.pi`) is confined to a small, fixed handful of lemmas.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit

open Real

noncomputable section

lemma kernelTailCap_le_two_div_51005 : kernelTailCap ≤ (2 : ℝ) / 51005 := by
  -- Convert the tail cap to `π^2 / 255025`.
  have hcap : kernelTailCap = (Real.pi ^ 2) / 255025 := kernelTailCap_eq_pi_sq_div_255025
  -- Use the standard bound `π < 3.15`.
  have hpi : (Real.pi : ℝ) < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 ≤ (Real.pi : ℝ) := (le_of_lt Real.pi_pos)
  have habs : |(Real.pi : ℝ)| < |(3.15 : ℝ)| := by
    have h3150 : 0 ≤ (3.15 : ℝ) := by norm_num
    simpa [abs_of_nonneg hpi0, abs_of_nonneg h3150] using hpi
  have hpi2_lt : (Real.pi : ℝ) ^ 2 < (3.15 : ℝ) ^ 2 := (sq_lt_sq).2 habs
  have h315 : (3.15 : ℝ) ^ 2 < 10 := by norm_num
  have hpi2_le : (Real.pi : ℝ) ^ 2 ≤ 10 := le_of_lt (lt_trans hpi2_lt h315)
  have hinv : 0 ≤ ((255025 : ℝ)⁻¹) := by
    have : 0 < (255025 : ℝ) := by norm_num
    exact le_of_lt (inv_pos.2 this)

  -- Divide by the positive denominator.
  have hdiv :
      ((Real.pi : ℝ) ^ 2) / 255025 ≤ (10 : ℝ) / 255025 := by
    -- Avoid `div_le_div_*` lemmas; use `mul_le_mul` with `inv_nonneg`.
    simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_right hpi2_le hinv)

  -- Rewrite `10/255025` as `2/51005`.
  have h10 : (10 : ℝ) / 255025 = (2 : ℝ) / 51005 := by norm_num

  -- Finish.
  simpa [hcap, h10] using hdiv

end

end Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
