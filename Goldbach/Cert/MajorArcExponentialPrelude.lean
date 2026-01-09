import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Basic complex-exponential estimates for major-arc style arguments.

These are small, self-contained lemmas about the additive character
`e(x) := exp(2π i x)` used in circle-method major-arc decompositions.
-/

namespace Goldbach.Cert.MajorArcExponential

noncomputable section

open Real

/-- Additive character `e(x) = exp(2π i x)` (with `x : ℝ`). -/
noncomputable def e (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * x))

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  simpa [e] using Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)

lemma norm_e_sub_e_le_of_abs_two_pi_mul_sub_le_one {x y : ℝ}
    (hxy : |2 * Real.pi * (x - y)| ≤ 1) :
    ‖e x - e y‖ ≤ 4 * Real.pi * |x - y| := by
  -- Factor out `e y` and reduce to `‖exp z - 1‖`.
  have hfactor :
      e x - e y
        =
      e y * (Complex.exp (Complex.I * (2 * Real.pi * (x - y))) - 1) := by
    -- `e x = e y * exp(2π i (x-y))`
    have hx :
        e x = e y * Complex.exp (Complex.I * (2 * Real.pi * (x - y))) := by
      -- `exp(A + B) = exp(A) * exp(B)` and `2πx = 2πy + 2π(x-y)`.
      have hmul :
          Complex.exp (Complex.I * (2 * Real.pi * y)) *
              Complex.exp (Complex.I * (2 * Real.pi * (x - y)))
            =
          Complex.exp
            ((Complex.I * (2 * Real.pi * y)) + (Complex.I * (2 * Real.pi * (x - y)))) := by
        exact
          (Complex.exp_add (Complex.I * (2 * Real.pi * y))
              (Complex.I * (2 * Real.pi * (x - y)))).symm
      have hadd :
          (Complex.I * (2 * Real.pi * y) : ℂ) + Complex.I * (2 * Real.pi * (x - y))
            =
          Complex.I * (2 * Real.pi * x) := by
        -- Algebra in the commutative ring `ℂ`.
        simp [sub_eq_add_neg, mul_add, mul_assoc, add_comm, add_left_comm]
      -- Put it together.
      calc
        e x = Complex.exp (Complex.I * (2 * Real.pi * x)) := by simp [e]
        _ = Complex.exp ((Complex.I * (2 * Real.pi * y)) + (Complex.I * (2 * Real.pi * (x - y)))) := by
              simp [hadd]
        _ = e y * Complex.exp (Complex.I * (2 * Real.pi * (x - y))) := by
              simpa [e, mul_assoc] using hmul.symm
    calc
      e x - e y
          = e y * Complex.exp (Complex.I * (2 * Real.pi * (x - y))) - e y * 1 := by
              simp [hx, mul_assoc]
      _ = e y * (Complex.exp (Complex.I * (2 * Real.pi * (x - y))) - 1) := by
              ring

  set z : ℂ := (Complex.I * (2 * Real.pi * (x - y)) : ℂ)
  have hz : ‖z‖ ≤ 1 := by
    -- `‖I * r‖ = |r|` for real `r`.
    have hz' : ‖z‖ = |2 * Real.pi * (x - y)| := by
      calc
        ‖z‖ = ‖(Complex.I : ℂ)‖ * ‖(2 * Real.pi * (x - y) : ℂ)‖ := by
              simp [z]
        _ = ‖(2 * Real.pi * (x - y) : ℂ)‖ := by simp
        _ = ‖2 * Real.pi * (x - y)‖ := by simpa using (Complex.norm_real (2 * Real.pi * (x - y)))
        _ = |2 * Real.pi * (x - y)| := by simp [Real.norm_eq_abs]
    simpa [hz'] using hxy

  have hsmall : ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ :=
    Complex.norm_exp_sub_one_le (x := z) hz

  calc
    ‖e x - e y‖
        = ‖e y * (Complex.exp z - 1)‖ := by
            simp [hfactor, z]
    _ = ‖e y‖ * ‖Complex.exp z - 1‖ := by
            simp
    _ ≤ 1 * (2 * ‖z‖) := by
            have : ‖e y‖ = 1 := norm_e y
            nlinarith [hsmall, this]
    _ = 4 * Real.pi * |x - y| := by
            -- `‖z‖ = |2π(x-y)| = (2π) * |x-y|`
            have hz' : ‖z‖ = |2 * Real.pi * (x - y)| := by
              calc
                ‖z‖ = ‖(Complex.I : ℂ)‖ * ‖(2 * Real.pi * (x - y) : ℂ)‖ := by
                      simp [z]
                _ = ‖(2 * Real.pi * (x - y) : ℂ)‖ := by simp
                _ = ‖2 * Real.pi * (x - y)‖ := by
                      simpa using (Complex.norm_real (2 * Real.pi * (x - y)))
                _ = |2 * Real.pi * (x - y)| := by simp [Real.norm_eq_abs]
            have h2pi_nonneg : 0 ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
            have habs : |2 * Real.pi * (x - y)| = (2 * Real.pi) * |x - y| := by
              calc
                |2 * Real.pi * (x - y)|
                    = |(2 * Real.pi) * (x - y)| := by simp [mul_assoc]
                _ = |2 * Real.pi| * |x - y| := by simp [abs_mul]
                _ = (2 * Real.pi) * |x - y| := by simp [abs_of_nonneg h2pi_nonneg]
            -- Now simplify arithmetically without expanding `|π|`.
            calc
              1 * (2 * ‖z‖) = 2 * ‖z‖ := by simp
              _ = 2 * |2 * Real.pi * (x - y)| := by simp [hz']
              _ = 2 * ((2 * Real.pi) * |x - y|) := by simp [habs]
              _ = 4 * Real.pi * |x - y| := by ring

end

end Goldbach.Cert.MajorArcExponential
