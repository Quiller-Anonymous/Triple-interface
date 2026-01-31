import SSU.Torus.Basic

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
Dyadic shells on the torus (`AddCircle 1`) using the circle distance to `0`.

Faithful replacement for TeX notation `|ξ|` on `𝕋`:

`|ξ|ₜ := dist ξ 0`.

This gives a canonical “radial” decomposition around frequency `0` that respects periodicity.
We use half-open real intervals (`Ioc`) to avoid overlaps (endpoints are measure-zero).
-/

namespace SSU
namespace Torus

open scoped BigOperators

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The torus “absolute value” `|ξ|ₜ := dist ξ 0` (distance to `0` on `AddCircle 1`). -/
def absT (ξ : UC) : ℝ :=
  dist ξ (0 : UC)

theorem absT_eq_norm (ξ : UC) : absT ξ = ‖ξ‖ := by
  simp [absT, dist_eq_norm]

theorem absT_nonneg (ξ : UC) : 0 ≤ absT ξ := by
  simp [absT]

/-- On `AddCircle 1`, the distance to `0` is always at most `1/2`. -/
theorem absT_le_half (ξ : UC) : absT ξ ≤ (1 : ℝ) / 2 := by
  -- `‖ξ‖ ≤ |1|/2` is `AddCircle.norm_le_half_period`.
  have h : ‖ξ‖ ≤ |(1 : ℝ)| / 2 := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := ξ) (by norm_num)
  simpa [absT_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 1)] using h

/-- Dyadic radius at shell index `j`, scaled by `1/H`: `2^{-j}/H`. -/
abbrev dyadicRadius (H : ℝ) (j : ℤ) : ℝ :=
  (2 : ℝ) ^ (-j) / H

/--
Dyadic torus shell (TeX: `2^{-(j+1)}/H < |ξ| ≤ 2^{-j}/H`) using `|ξ|ₜ := dist ξ 0`.

We use `Ioc` to make shells disjoint.
-/
def dyadicShell (H : ℝ) (j : ℤ) : Set UC :=
  (fun ξ : UC => absT ξ) ⁻¹' Set.Ioc (dyadicRadius H (j + 1)) (dyadicRadius H j)

@[simp]
theorem mem_dyadicShell (H : ℝ) (j : ℤ) (ξ : UC) :
    ξ ∈ dyadicShell H j ↔ absT ξ ∈ Set.Ioc (dyadicRadius H (j + 1)) (dyadicRadius H j) :=
  Iff.rfl

theorem measurable_absT : Measurable (fun ξ : UC => absT ξ) := by
  -- `ξ ↦ dist ξ 0` is continuous, hence measurable.
  have hcont : Continuous (fun ξ : UC => dist ξ (0 : UC)) := continuous_id.dist continuous_const
  simpa [absT] using hcont.measurable

theorem measurableSet_dyadicShell (H : ℝ) (j : ℤ) : MeasurableSet (dyadicShell H j) := by
  -- Measurability is inherited from `absT` and the real interval `Ioc`.
  exact measurableSet_preimage (measurable_absT) measurableSet_Ioc

end

end Torus
end SSU
