import Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds

/-!
The fixed-`Q0` truncation on even inputs is concentrated in its first three
nonconstant odd Ramanujan modes. This is a structural consequence of grouping
the moduli `r` and `2*r`, not an observation about a single window.
-/

namespace Goldbach.Cert.MajorArcModules.Q0SigmaTruncLowModeConcentration

open Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds

/-- The exact full-period variance contributed by odd cores `3`, `5`, and `7`. -/
def lowModeVarianceRat : ℚ :=
  (evenMultiplicity 3) ^ 2 / (totientFast 3 : ℚ) ^ 3
    + (evenMultiplicity 5) ^ 2 / (totientFast 5 : ℚ) ^ 3
    + (evenMultiplicity 7) ^ 2 / (totientFast 7 : ℚ) ^ 3

theorem lowModeVarianceRat_eq : lowModeVarianceRat = (251 : ℚ) / 432 := by
  simp only [lowModeVarianceRat, totientFast_eq]
  norm_num [evenMultiplicity, cutoff,
    Nat.totient_prime (by decide : Nat.Prime 3),
    Nat.totient_prime (by decide : Nat.Prime 5),
    Nat.totient_prime (by decide : Nat.Prime 7)]

/-- The three displayed modes are terms of the nonnegative variance sum. -/
theorem lowModeVarianceRat_le_varianceRat : lowModeVarianceRat ≤ varianceRat := by
  native_decide

/-- More than `96.52%` of the exact full-period variance lies in odd cores `3,5,7`. -/
theorem lowModeVarianceRat_gt_9652_permyriad :
    (9652 : ℚ) / 10000 * varianceRat < lowModeVarianceRat := by
  rw [lowModeVarianceRat_eq]
  have h := varianceRat_lt
  linarith

/-- The variance outside odd cores `3,5,7` is below `0.020906`. -/
theorem varianceRat_sub_lowModeVarianceRat_lt :
    varianceRat - lowModeVarianceRat < (17639 : ℚ) / 843750 := by
  rw [lowModeVarianceRat_eq]
  have h := varianceRat_lt
  linarith

end Goldbach.Cert.MajorArcModules.Q0SigmaTruncLowModeConcentration
