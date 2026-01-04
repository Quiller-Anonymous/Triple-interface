/-
  Twin/Compat.lean
  -----------------
  Small, stable helpers shared across the Twin subtree.
  • Proved √-facts (no axioms for sqrt).
  • Re-export a couple of LedgerExtra lemmas by name (no redefinition).
  • Optional axiom for SS ≥ 0 (replace by a proof if you have it).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Twin.LedgerExtra
import Twin.GoalAPI
import Twin.SingularSeries

namespace Twin
namespace Compat

open Real

/-! ## √-helpers (proved) -/

/-! ## Positivity of the truncated singular series -/
theorem truncSS_nonneg_of_ge3
  (S : Finset ℕ) (hS : ∀ p ∈ S, 3 ≤ p) :
  0 ≤ truncSingularSeries S :=
  Twin.truncSingularSeries_nonneg_of_ge_three (S := S) hS

/-- For `a,b ≥ 0`, we have `sqrt (a+b) ≤ sqrt a + sqrt b`. -/
lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sqrt (a + b) ≤ sqrt a + sqrt b := by
  -- Use `Real.sqrt_le_iff : sqrt x ≤ y ↔ 0 ≤ y ∧ x ≤ y^2`.
  have hy : 0 ≤ sqrt a + sqrt b :=
    add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  -- Show `a + b ≤ (sqrt a + sqrt b)^2`.
  have hnonneg : 0 ≤ 2 * (sqrt a * sqrt b) := by
    have : 0 ≤ sqrt a * sqrt b :=
      mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
    exact mul_nonneg (by norm_num) this
  have hstep : a + b ≤ a + b + 2 * (sqrt a * sqrt b) :=
    by simpa [add_comm, add_left_comm, add_assoc]
       using (le_add_of_nonneg_right hnonneg :
              a + b ≤ (a + b) + 2 * (sqrt a * sqrt b))
  have hmain : a + b ≤ (sqrt a + sqrt b) ^ 2 := by
    simpa [pow_two, two_mul, mul_add, add_mul,
           Real.mul_self_sqrt ha, Real.mul_self_sqrt hb,
           mul_comm, mul_left_comm, mul_assoc,
           add_comm, add_left_comm, add_assoc]
      using hstep
  exact (Real.sqrt_le_iff).mpr ⟨hy, hmain⟩

/-- For `a,b ≥ 0`, we have `sqrt (a * b) = sqrt a * sqrt b`.

    Proof avoids `Real.sqrt_mul` and `le_sqrt_iff`; compare squares
    and use `sq_le_sq ↔ abs` plus nonnegativity to drop `|·|`. -/
lemma sqrt_mul_split_of_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sqrt (a * b) = sqrt a * sqrt b := by
  -- Nonnegativity of both sides
  have L : 0 ≤ sqrt (a * b) := sqrt_nonneg _
  have R : 0 ≤ sqrt a * sqrt b :=
    mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  -- Squares of both sides are equal to `a*b`
  have hL2 : (sqrt (a * b)) ^ 2 = a * b := by
    have hab : 0 ≤ a * b := mul_nonneg ha hb
    simpa [pow_two] using Real.mul_self_sqrt hab
  have hR2 : (sqrt a * sqrt b) ^ 2 = a * b := by
    simp [pow_two, Real.mul_self_sqrt ha, Real.mul_self_sqrt hb,
          mul_comm, mul_left_comm, mul_assoc]
  -- From equality of squares, get ≤ both ways via `sq_le_sq` and drop abs
  have h1sq : (sqrt (a * b)) ^ 2 ≤ (sqrt a * sqrt b) ^ 2 := by
    simpa [hL2, hR2] using (le_of_eq hR2.symm)
  have h2sq : (sqrt a * sqrt b) ^ 2 ≤ (sqrt (a * b)) ^ 2 := by
    simpa [hL2, hR2] using (le_of_eq hR2)
  have h1abs : |sqrt (a * b)| ≤ |sqrt a * sqrt b| := (sq_le_sq).1 h1sq
  have h2abs : |sqrt a * sqrt b| ≤ |sqrt (a * b)| := (sq_le_sq).1 h2sq
  have h1 : sqrt (a * b) ≤ sqrt a * sqrt b := by
    simpa [abs_of_nonneg L, abs_of_nonneg R] using h1abs
  have h2 : sqrt a * sqrt b ≤ sqrt (a * b) := by
    simpa [abs_of_nonneg R, abs_of_nonneg L] using h2abs
  exact le_antisymm h1 h2

/-! ## Re-exports from Twin.LedgerExtra (names only; not redefined here) -/
export Twin.LedgerExtra
  ( window_l1_le_sqrt_span_mul_window_l2
    sqrt_span_mul_sqrt_span_div9 )

end Compat
end Twin
