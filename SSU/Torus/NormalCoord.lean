import SSU.Torus.Basic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
Signed “wrap-around” coordinates on `𝕋 = AddCircle 1`.

This is the Lean-realistic version of TeX’s signed normal coordinate `ν_I(ξ)` used in
`05b_SSU.tex` (tube-overlap block): represent a torus difference in the fundamental domain
`(-1/2, 1/2]`.

We build it from Mathlib’s measurable equivalence
`AddCircle 1 ≃ᵐ Ioc a (a+1)` (see `MeasureTheory/Integral/IntervalIntegral/Periodic`).
-/

namespace SSU
namespace Torus

open MeasureTheory AddCircle

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The half-open fundamental domain `(-1/2, 1/2]`. -/
abbrev halfIoc : Set ℝ :=
  Set.Ioc (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + (1 : ℝ))

/--
Measurable fundamental-domain representative `AddCircle 1 → (-1/2, 1/2]`.

This is `equivIoc 1 (-1/2)` upgraded to a measurable equivalence.
-/
noncomputable def wrapIocHalf : UC ≃ᵐ Set.Ioc (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + (1 : ℝ)) :=
  AddCircle.measurableEquivIoc (T := (1 : ℝ)) (a := (-(1 : ℝ) / 2))

@[simp]
theorem wrapIocHalf_apply_coe (x : ℝ)
    (hx : x ∈ Set.Ioc (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + (1 : ℝ))) :
    wrapIocHalf (↑x : UC) = ⟨x, hx⟩ := by
  -- On the fundamental domain, `equivIoc` is literally the inclusion.
  simpa [wrapIocHalf, AddCircle.measurableEquivIoc, AddCircle.equivIoc_coe_eq hx]

/-- The signed “wrap-around” coordinate `wrapHalf(ξ) ∈ (-1/2, 1/2]`. -/
def wrapHalf (ξ : UC) : ℝ :=
  (wrapIocHalf ξ).1

theorem wrapHalf_mem (ξ : UC) :
    wrapHalf ξ ∈ Set.Ioc (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + (1 : ℝ)) :=
  (wrapIocHalf ξ).2

theorem measurable_wrapHalf : Measurable wrapHalf := by
  -- `wrapHalf = Subtype.val ∘ wrapIocHalf`.
  simpa [wrapHalf, Function.comp] using
    ((measurable_subtype_coe).comp (wrapIocHalf.measurable))

/--
Signed normal coordinate to the “arc centered at `c`”:
`ν_c(ξ) := wrapHalf(ξ - c) ∈ (-1/2, 1/2]`.

This is the concrete choice recommended for SSU’s Fejér-banked tube construction.
-/
def normalCoord (c : UC) : UC → ℝ :=
  fun ξ => wrapHalf (ξ - c)

theorem normalCoord_mem (c ξ : UC) :
    normalCoord c ξ ∈ Set.Ioc (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + (1 : ℝ)) := by
  simpa [normalCoord] using wrapHalf_mem (ξ - c)

theorem measurable_normalCoord (c : UC) : Measurable (normalCoord c) := by
  -- `ξ ↦ ξ - c` is continuous, hence measurable; compose with `wrapHalf`.
  have hsub : Measurable fun ξ : UC => ξ - c := (continuous_id.sub continuous_const).measurable
  simpa [normalCoord] using measurable_wrapHalf.comp hsub

end

end Torus
end SSU
