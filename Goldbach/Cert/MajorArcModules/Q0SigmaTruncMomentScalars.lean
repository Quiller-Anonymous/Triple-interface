import Goldbach.Cert.MajorArcModules.Q0SigmaTruncEvenDivisor

/-! The exact mean and diagonal variance scalars for the even Ramanujan expansion. -/

namespace Goldbach.Cert.MajorArcModules.Q0SigmaTruncMomentScalars

open scoped BigOperators
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds

theorem oddWeightRat_one : oddWeightRat 1 = 2 := by
  norm_num [oddWeightRat, evenMultiplicity, totientFast_eq, cutoff]

theorem oddWeightRat_one_cast : (oddWeightRat 1 : ℝ) = 2 := by
  rw [oddWeightRat_one]
  norm_num

theorem oddWeightRat_square_mul_totient (r : ℕ) (hr : 0 < r) :
    oddWeightRat r ^ 2 * (Nat.totient r : ℚ) =
      if Odd r ∧ Squarefree r then
        evenMultiplicity r ^ 2 / (totientFast r : ℚ) ^ 3 else 0 := by
  by_cases hs : Odd r ∧ Squarefree r
  · have hphi : (Nat.totient r : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.totient_pos.mpr hr)
    simp only [oddWeightRat, if_pos hs, totientFast_eq]
    field_simp
  · simp [oddWeightRat, hs]

theorem sum_oddWeightRat_square_mul_totient :
    (∑ r ∈ Finset.Icc 1 cutoff, oddWeightRat r ^ 2 * (Nat.totient r : ℚ)) =
      4 + varianceRat := by
  have hset : Finset.Icc 1 cutoff = insert 1 (Finset.Icc 2 cutoff) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    dsimp [cutoff]
    omega
  have hnot : 1 ∉ Finset.Icc 2 cutoff := by simp
  rw [hset, Finset.sum_insert hnot]
  have hrest :
      (∑ r ∈ Finset.Icc 2 cutoff, oddWeightRat r ^ 2 * (Nat.totient r : ℚ)) =
        varianceRat := by
    unfold varianceRat
    apply Finset.sum_congr rfl
    intro r hr
    exact oddWeightRat_square_mul_totient r (by have := (Finset.mem_Icc.mp hr).1; omega)
  rw [hrest, oddWeightRat_one]
  norm_num

theorem sum_oddWeightRat_square_mul_totient_cast :
    (∑ r ∈ Finset.Icc 1 cutoff, (oddWeightRat r : ℝ) ^ 2 * (Nat.totient r : ℝ)) =
      4 + (varianceRat : ℝ) := by
  exact_mod_cast sum_oddWeightRat_square_mul_totient

theorem oddWeightRat_mul_totient (r : ℕ) (hr : 0 < r) :
    oddWeightRat r * (Nat.totient r : ℚ) =
      if Odd r ∧ Squarefree r then
        evenMultiplicity r / (totientFast r : ℚ) else 0 := by
  by_cases hs : Odd r ∧ Squarefree r
  · have hphi : (Nat.totient r : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.totient_pos.mpr hr)
    simp only [oddWeightRat, if_pos hs, totientFast_eq]
    field_simp
  · simp [oddWeightRat, hs]

theorem sum_oddWeightRat_mul_totient :
    (∑ r ∈ Finset.Icc 1 cutoff, oddWeightRat r * (Nat.totient r : ℚ)) =
      valueAtZeroRat := by
  unfold valueAtZeroRat
  apply Finset.sum_congr rfl
  intro r hr
  exact oddWeightRat_mul_totient r (Finset.mem_Icc.mp hr).1

theorem sum_oddWeightRat_mul_totient_cast :
    (∑ r ∈ Finset.Icc 1 cutoff, (oddWeightRat r : ℝ) * (Nat.totient r : ℝ)) =
      (valueAtZeroRat : ℝ) := by
  exact_mod_cast sum_oddWeightRat_mul_totient

end Goldbach.Cert.MajorArcModules.Q0SigmaTruncMomentScalars
