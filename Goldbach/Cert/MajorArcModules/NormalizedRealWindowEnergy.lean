import Mathlib
import Goldbach.Cert.MajorArcModules.DivisorWindowDiscrepancy

/-! Centering and real normalization for complex-valued window energy. -/

namespace Goldbach.Cert.MajorArcModules.NormalizedRealWindowEnergy

open scoped BigOperators

theorem centered_normalized_energy_le_reference {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) (c r : ℝ) :
    (∑ n ∈ s, ‖((f n / c : ℝ) : ℂ) -
        (s.card : ℂ)⁻¹ * ∑ j ∈ s, ((f j / c : ℝ) : ℂ)‖ ^ 2)
      ≤ (∑ n ∈ s, (f n - r) ^ 2) / c ^ 2 := by
  classical
  by_cases hs : s = ∅
  · subst s
    simp
  have hm : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  let μ : ℝ := (∑ j ∈ s, f j) / s.card
  have hmean : (∑ n ∈ s, f n) = (s.card : ℝ) * μ := by
    dsimp [μ]
    field_simp
  have havg : (s.card : ℂ)⁻¹ * ∑ j ∈ s, ((f j / c : ℝ) : ℂ)
      = ((μ / c : ℝ) : ℂ) := by
    rw [show (s.card : ℂ) = ((s.card : ℝ) : ℂ) by simp,
      ← Complex.ofReal_inv, ← Complex.ofReal_sum, ← Complex.ofReal_mul]
    congr 1
    dsimp [μ]
    rw [← Finset.sum_div]
    ring
  have hpoint (n : ι) :
      ‖((f n / c : ℝ) : ℂ) -
        (s.card : ℂ)⁻¹ * ∑ j ∈ s, ((f j / c : ℝ) : ℂ)‖ ^ 2
        = (f n - μ) ^ 2 / c ^ 2 := by
    rw [havg, ← Complex.ofReal_sub, ← sub_div]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
  simp_rw [hpoint]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (Goldbach.Cert.DivisorWindowDiscrepancy.centered_energy_le_reference s f μ r hmean)
    (sq_nonneg c)

end Goldbach.Cert.MajorArcModules.NormalizedRealWindowEnergy
