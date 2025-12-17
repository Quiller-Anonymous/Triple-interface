import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Goldbach
namespace Compat

open scoped BigOperators
open Real

/-! ## 1. Absolute value / nonneg helpers -/

/-- If `x ≥ 0` then `|x| = x`. Kept here to avoid hunting names per snapshot. -/
@[simp] lemma abs_of_nonneg' {x : ℝ} (hx : 0 ≤ x) : |x| = x := abs_of_nonneg hx

/-- If `x ≥ 0` and `y ≥ 0` then `|x * y| = x * y`. -/
@[simp] lemma abs_mul_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  |x * y| = x * y := by
  simpa [abs_of_nonneg' hx, abs_of_nonneg' hy, mul_comm, mul_left_comm, mul_assoc] using
    (abs_mul x y)

/-! ## 2. Square–root algebra -/

/-- `√(a*b) = √a * √b` under nonnegativity. -/
lemma sqrt_mul' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
  sqrt (a * b) = sqrt a * sqrt b := by
  -- This is stable across snapshots; `Real.sqrt_mul` expects nonneg hypotheses.
  simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.sqrt_mul ha b)

/-- `√(a^2) = |a|`. A direct name for convenience. -/
@[simp] lemma sqrt_sq_eq_abs' (a : ℝ) : sqrt (a ^ 2) = |a| := by
  simpa [pow_two] using Real.sqrt_sq_eq_abs a

/-- `√((a*b)^2) = |a|*|b|`. -/
@[simp] lemma sqrt_sq_mul_abs (a b : ℝ) : sqrt ((a * b) ^ 2) = |a| * |b| := by
  simpa [pow_two, abs_mul, mul_comm, mul_left_comm, mul_assoc] using sqrt_sq_eq_abs' (a * b)

/-- If `0 ≤ x` then `√(x/9) = √x / 3`. -/
lemma sqrt_div_by9 {x : ℝ} (hx : 0 ≤ x) : sqrt (x / 9) = sqrt x / 3 := by
  -- Write `x/9 = x * (1/9)` and use `√(x*(1/9)) = √x * √(1/9)`, then `√(1/9)=1/3`.
  have h9pos : (0 : ℝ) < 9 := by norm_num
  have h1o9_nonneg : 0 ≤ (1 / 9 : ℝ) := by positivity
  have h1o3_pos  : (0 : ℝ) < 3 := by norm_num
  have : sqrt (x * (1/9)) = sqrt x * sqrt (1/9) :=
    sqrt_mul' hx (by positivity)
  -- Also `sqrt (1/9) = 1/3` because `1/9 = (1/3)^2`.
  have h_sqrt_1o9 : sqrt (1/9 : ℝ) = 1/3 := by
    have : (1/9 : ℝ) = (1/3)^2 := by
      ring_nf
    -- Now `√((1/3)^2) = |1/3| = 1/3` as `1/3>0`.
    simpa [this, sqrt_sq_eq_abs', abs_of_pos h1o3_pos]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simp only [one_div] at this h_sqrt_1o9
  rw [this, h_sqrt_1o9]

/-! ## 3. Tiny normalizations around `(H+1)/9` and squares -/

/-- `(↑H + 1) * ((↑H + 1) / 9) = (↑H + 1) * (↑H + 1) / 9`. -/
lemma span_mul_div9 (H : ℕ) :
  ( (H : ℝ) + 1) * (( (H : ℝ) + 1) / 9) = (( (H : ℝ) + 1) * ((H : ℝ) + 1)) / 9 := by
  field_simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- `((↑H + 1)/3)^2 = ((↑H+1) * (↑H+1)) / 9`. -/
lemma span_over_three_sq (H : ℕ) :
  (( (H : ℝ) + 1) / 3) ^ 2 = (( (H : ℝ) + 1) * ((H : ℝ) + 1)) / 9 := by
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have : (( (H : ℝ) + 1) / 3) ^ 2 = (( (H : ℝ) + 1) ^ 2) / (3 ^ 2) := by
    field_simp [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
  -- now `((H+1)^2)/(3^2) = ((H+1)*(H+1))/9`
  have : (( (H : ℝ) + 1) / 3) ^ 2 = (( (H : ℝ) + 1) * ((H : ℝ) + 1)) / 9 := by
    have h : (3 : ℝ) ^ 2 = (9 : ℝ) := by norm_num
    simpa [pow_two, h, mul_comm, mul_left_comm, mul_assoc] using this
  simpa using this

/-- `√((↑H+1) * ((↑H+1)/9)) = (↑H+1)/3` for natural `H`. -/
lemma sqrt_span_mul_span_div9 (H : ℕ) :
  sqrt ( ((H : ℝ) + 1) * (((H : ℝ) + 1) / 9) ) = ((H : ℝ) + 1) / 3 := by
  have hH : 0 ≤ ((H : ℝ) + 1) := by positivity
  -- `√( (H+1)*((H+1)/9) ) = √(H+1) * √((H+1)/9)`
  have h : sqrt ( ((H : ℝ) + 1) * (((H : ℝ) + 1) / 9) )
           = sqrt ((H : ℝ) + 1) * sqrt (((H : ℝ) + 1) / 9) :=
    sqrt_mul' hH (by have := div_nonneg hH (by norm_num : (0:ℝ) ≤ 9); simpa using this)
  -- And `√((H+1)/9) = √(H+1)/3`
  have h' : sqrt (((H : ℝ) + 1) / 9) = sqrt ((H : ℝ) + 1) / 3 :=
    sqrt_div_by9 (by exact hH)
  -- Multiply and simplify
  rw [h, h']
  -- `√(H+1) * (√(H+1)/3) = (H+1)/3`
  have hpos : 0 ≤ sqrt ((H : ℝ) + 1) := by exact sqrt_nonneg _
  calc
    sqrt ((H : ℝ) + 1) * (sqrt ((H : ℝ) + 1) / 3)
        = (sqrt ((H : ℝ) + 1))^2 / 3 := by ring_nf
    _   = ((H : ℝ) + 1) / 3 := by rw [sq_sqrt hH]


namespace Twin
namespace LedgerExtra

-- bring the lemmas into this namespace with the names BankPieces / AnalyticAssemble use
export Goldbach.Compat
  ( abs_of_nonneg'        -- |x| = x when x ≥ 0
    abs_mul_of_nonneg     -- |x*y| = x*y when x,y ≥ 0
    sqrt_mul'             -- √(a*b) = √a * √b   (under nonneg)
    sqrt_sq_eq_abs'       -- √(a^2) = |a|
    sqrt_sq_mul_abs       -- √((a*b)^2) = |a|*|b|
    sqrt_div_by9          -- √(x/9) = √x / 3   (x ≥ 0)
    span_mul_div9         -- (H+1)*((H+1)/9) = ((H+1)*(H+1))/9
    span_over_three_sq    -- ((H+1)/3)^2 = ((H+1)*(H+1))/9
    sqrt_span_mul_span_div9 -- √((H+1)*((H+1)/9)) = (H+1)/3
  )

end LedgerExtra
end Twin


end Compat
end Goldbach
