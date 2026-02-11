import SSU.Engines.TypeII
import Mathlib.Data.Real.Sqrt

/-!
Small deterministic helper lemmas used when combining Step 3/4 large-sieve estimates.

These are “pure inequalities” that match the TeX bookkeeping and are independent of any
Montgomery–Vaughan large sieve proof.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

theorem tubeEnergy_nonneg (T : Finset TubePoint) (F : TubePoint → ℂ) :
    0 ≤ _root_.SSU.tubeEnergy T F := by
  classical
  unfold _root_.SSU.tubeEnergy
  refine Finset.sum_nonneg ?_
  intro p hp
  positivity

/-!
### A “max trick” for the Step 3–4 geometric mean

For `x ≥ 0` we have

`U/q + x ≤ max(U/(qD), 1) * (D + x)`.

This is the deterministic inequality used to trade the Step-4 factor `U/q + x`
for the TeX-shaped factor `D + x` at the cost of a `TubeData`-dependent constant.
-/

theorem add_div_le_max_mul_add (U D q x : ℝ) (hq : 0 < q) (hD : 0 < D) (hx : 0 ≤ x) :
    (U / q + x) ≤ (max (U / (q * D)) 1) * (D + x) := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hD0 : D ≠ 0 := ne_of_gt hD
  by_cases hUD : U / (q * D) ≤ (1 : ℝ)
  · have hmax : max (U / (q * D)) 1 = (1 : ℝ) := max_eq_right hUD
    have hU_le : U / q ≤ D := by
      have hqD : 0 < q * D := mul_pos hq hD
      have : U ≤ q * D := (div_le_one (show 0 < q * D from hqD)).1 hUD
      have := (div_le_iff₀' hq).2 this
      -- `U ≤ q*D` → `U/q ≤ D`.
      simpa [mul_assoc, div_eq_mul_inv, hq0] using this
    simpa [hmax, add_le_add_iff_right] using add_le_add_right hU_le x
  · have hUD_ge : (1 : ℝ) ≤ U / (q * D) := le_of_not_ge hUD
    have hmax : max (U / (q * D)) 1 = U / (q * D) := max_eq_left hUD_ge
    have hx' : x ≤ (U / (q * D)) * x := by
      simpa [one_mul] using (mul_le_mul_of_nonneg_right hUD_ge hx)
    have : U / q + x ≤ U / q + (U / (q * D)) * x := add_le_add_left hx' (U / q)
    have hmulD : (U / (q * D)) * D = U / q := by
      field_simp [hq0, hD0]
    have hrewrite :
        U / q + (U / (q * D)) * x = (U / (q * D)) * (D + x) := by
      calc
        U / q + (U / (q * D)) * x = (U / (q * D)) * D + (U / (q * D)) * x := by
          simpa [hmulD] using rfl
        _ = (U / (q * D)) * (D + x) := by
          simp [mul_add]
    simpa [hmax, hrewrite] using this

theorem sqrt_add_div_le
    (U D q x : ℝ) (hq : 0 < q) (hD : 0 < D) (hx : 0 ≤ x) :
    Real.sqrt (U / q + x)
      ≤ Real.sqrt (max (U / (q * D)) 1) * Real.sqrt (D + x) := by
  have hxratio : (U / q + x) ≤ (max (U / (q * D)) 1) * (D + x) :=
    add_div_le_max_mul_add (U := U) (D := D) (q := q) (x := x) hq hD hx
  have hmul :
      Real.sqrt ((max (U / (q * D)) 1) * (D + x))
        =
      Real.sqrt (max (U / (q * D)) 1) * Real.sqrt (D + x) := by
    have : 0 ≤ max (U / (q * D)) 1 := by positivity
    have : 0 ≤ D + x := by positivity
    simpa [mul_assoc] using (Real.sqrt_mul this (D + x)).symm
  simpa [hmul] using Real.sqrt_le_sqrt hxratio

end

end LargeSieve
end TypeII
end Engines
end SSU
