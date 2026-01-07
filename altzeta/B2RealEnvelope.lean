import AltZeta.B2RealParams
import Mathlib.Data.Real.Sqrt

/-!
AltZeta/B2RealEnvelope.lean
===========================

Canonical envelope functions for the B2 workflow, tied to the “real parameter” pack.
-/

noncomputable section

namespace AltZeta
namespace B2

open Real

/-- Canonical truncation/full error envelope: `CΓ + √x · S_cert`. -/
def ETrunc0 (x : ℝ) : ℝ :=
  CGamma0 + Real.sqrt x * S0

lemma ETrunc0_nonneg (x : ℝ) : 0 ≤ ETrunc0 x := by
  have hCG : 0 ≤ CGamma0 := Goldbach.Census.CGamma_nonneg
  have hS : 0 ≤ S0 := Goldbach.Census.S_cert_nonneg
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hprod : 0 ≤ Real.sqrt x * S0 := mul_nonneg hsqrt hS
  simpa [ETrunc0] using add_nonneg hCG hprod

lemma ETrunc0_pos (x : ℝ) (hx : ValidX W0 x) : 0 < ETrunc0 x := by
  -- `CGamma0 = 1/4` is strictly positive; the sqrt term is nonnegative.
  have hCG : 0 < CGamma0 := by
    simpa [CGamma0, Goldbach.Census.CGamma_value] using (by norm_num : (0 : ℝ) < (1 : ℝ) / 4)
  have hS : 0 ≤ Real.sqrt x * S0 := by
    have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hS0 : 0 ≤ S0 := Goldbach.Census.S_cert_nonneg
    exact mul_nonneg hsqrt hS0
  have : 0 < CGamma0 + Real.sqrt x * S0 :=
    lt_of_lt_of_le (by simpa using hCG) (le_add_of_nonneg_right hS)
  simpa [ETrunc0] using this

end B2
end AltZeta

