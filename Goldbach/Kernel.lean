import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

open Real MeasureTheory Set Filter

/-! # Concrete Short-Shift Kernel -/

variable {H : ℝ}

/--
**The Fejér Density**
The Fourier transform of the kernel. A triangle function supported in [-1/H, 1/H].
Formula: H * (1 - |H * xi|)
-/
def FejerDensity (H : ℝ) (xi : ℝ) : ℝ :=
  H * (1 - abs (H * xi))

/--
**The Concrete Kernel K_H**
Defined explicitly as the inverse Fourier transform of the Fejér density.
-/
noncomputable def KH_Concrete (H : ℝ) (t : ℝ) : ℝ :=
  ∫ xi in Icc (-1/H) (1/H), (FejerDensity H xi) * cos (2 * π * t * xi)

/--
**Property: Non-negativity**
For H > 0, the density is non-negative on its support [-1/H, 1/H].
-/
lemma FejerDensity_nonneg (hH : 0 < H) :
    ∀ ξ ∈ Icc (-1/H) (1/H), 0 ≤ FejerDensity H ξ :=
by
  intros ξ hξ
  rw [mem_Icc] at hξ
  dsimp [FejerDensity]

  -- We need H * (1 - |Hξ|) >= 0
  -- Since H > 0, we need 1 >= |Hξ|
  apply mul_nonneg (le_of_lt hH)
  rw [sub_nonneg, abs_le]

  -- |Hξ| <= 1 <-> -1 <= Hξ <= 1
  -- We know -1/H <= ξ <= 1/H
  -- Multiply by H (positive)
  rcases hξ with ⟨h_left, h_right⟩
  constructor
  · rw [le_div_iff hH, neg_mul_eq_neg_mul] at h_left
    linarith
  · rw [div_le_iff hH] at h_right
    linarith

/--
**Property: L1 Mass**
We prove the total mass is exactly 1.
∫_{-1/H}^{1/H} H(1 - |Hξ|) dξ = 1
-/
theorem KH_mass_proof (hH : 0 < H) :
  ∫ xi in Icc (-1/H) (1/H), FejerDensity H xi = 1 :=
by
  dsimp [FejerDensity]

  -- 1. Pull H out
  rw [integral_mul_left]

  -- 2. Use interval integral properties to evaluate ∫ (1 - |Hξ|)
  -- Let u = Hξ. Then du = H dξ. Range becomes [-1, 1].
  -- In Mathlib, we use `integral_comp_mul_right` for u-substitution of linear scaling.

  -- Convert set integral (Icc) to interval integral
  rw [intervalIntegral.integral_of_le]
  · -- Transform: ξ -> 1 - |Hξ|
    -- We want to map this to ∫_{-1}^{1} (1 - |u|) * (1/H) du

    -- Let f(u) = 1 - |u|. We are integrating f(H * ξ).
    let f := λ u => 1 - abs u

    -- Use the scaling lemma: ∫ (f(c*x)) dx = (1/c) * ∫ f(u) du
    -- We need to align the bounds: -1/H * H = -1, 1/H * H = 1.
    have scale : ∫ ξ in (-1/H)..(1/H), f (H * ξ) = (H⁻¹) * ∫ u in (-1)..1, f u := by
      -- The bounds match exactly because H > 0
      have b1 : -1/H * H = -1 := by field_simp; ring
      have b2 : 1/H * H = 1 := by field_simp

      -- Apply integral_comp_mul_right with c = H
      rw [←b1, ←b2]
      rw [intervalIntegral.integral_comp_mul_right (λ x => 1 - abs x) (ne_of_gt hH)]
      field_simp

    rw [scale]

    -- Now we just calculate H * (1/H * ∫_{-1}^{1} (1-|u|))
    rw [←mul_assoc, mul_inv_cancel (ne_of_gt hH), one_mul]

    -- Evaluate ∫_{-1}^{1} (1 - |u|) du
    -- Split into ∫_{-1}^{0} (1 - (-u)) + ∫_{0}^{1} (1 - u)
    rw [intervalIntegral.integral_sub_abs_of_nonneg_of_le (by norm_num) (by norm_num) zero_le_one]

    -- Result is 1^2 = 1.
    simp

  · -- Bounds check for Icc to interval conversion
    apply le_trans
    · apply neg_le_of_abs_le
      rw [abs_div, abs_eq_self.mpr (le_of_lt hH), abs_neg, abs_one]
      apply one_div_le_one_div_of_le hH (by linarith) -- H >= 1 usually, but here just order
      -- Actually simpler: -1/H < 0 < 1/H
      apply le_trans (div_neg_of_neg_of_pos (by norm_num) hH) (le_of_lt (div_pos (by norm_num) hH))
    · rfl
