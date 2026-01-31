import SSU.Torus.Basic
import Mathlib.MeasureTheory.Function.Holder

/-!
Torus-side multiplier operators on `L²(AddCircle 1)`.

This is a small deterministic building block: if `φ ∈ L^∞`, then pointwise multiplication
`f ↦ φ • f` defines a bounded linear operator on `L²`.
-/

namespace SSU
namespace Torus

open scoped ENNReal

open MeasureTheory

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- `L²` on the SSU torus `AddCircle 1`, with respect to Haar measure. -/
abbrev L2 : Type := Lp ℂ (2 : ℝ≥0∞) μ

/-- `L^∞` on the SSU torus `AddCircle 1`, with respect to Haar measure. -/
abbrev Linf : Type := Lp ℂ (∞ : ℝ≥0∞) μ

namespace Multipliers

variable (φ : Linf)

local notation "p∞" => (∞ : ℝ≥0∞)
local notation "p2" => (2 : ℝ≥0∞)

/-- Linear map `f ↦ φ • f` on `L²`. -/
noncomputable def mulL2ₗ : L2 →ₗ[ℂ] L2 where
  toFun f := (φ • f : L2)
  map_add' f g := by
    simpa using (MeasureTheory.Lp.add_smul (f := φ) (g₁ := f) (g₂ := g))
  map_smul' c f := by
    simpa using
      (MeasureTheory.Lp.smul_comm (μ := μ) (p := p∞) (q := p2) (r := p2)
          (c := c) (f := φ) (g := f)).symm

/-- Bounded linear operator `f ↦ φ • f` on `L²`. -/
noncomputable def mulL2 : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous (mulL2ₗ (φ := φ)) ‖φ‖ fun f => by
    have h := (MeasureTheory.Lp.norm_smul_le (μ := μ) (p := p∞) (q := p2) (r := p2)
      (f := φ) (g := f))
    simpa using h

@[simp]
theorem mulL2_apply (f : L2) : mulL2 (φ := φ) f = (φ • f : L2) :=
  rfl

theorem norm_mulL2_apply_le (f : L2) : ‖mulL2 (φ := φ) f‖ ≤ ‖φ‖ * ‖f‖ := by
  simpa [mulL2_apply (φ := φ) (f := f)] using
    (MeasureTheory.Lp.norm_smul_le (μ := μ) (p := p∞) (q := p2) (r := p2) (f := φ) (g := f))

end Multipliers

/--
Pointwise multiplier operator on `L²` from an `L^∞` function `φ`.

This is just `Multipliers.mulL2` applied to the `L^∞` class of `φ`.
-/
noncomputable def toLinf (φ : UC → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ) : Linf :=
  (hφ.toLp φ : Linf)

/--
Multiplication operator on `L²` induced by a measurable bounded function `φ : UC → ℂ`.
-/
noncomputable def mulL2Op (φ : UC → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ) : L2 →L[ℂ] L2 :=
  Multipliers.mulL2 (φ := (toLinf (φ := φ) hφ))

@[simp]
theorem mulL2Op_apply (φ : UC → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (f : L2) :
    mulL2Op (φ := φ) hφ f = ((toLinf (φ := φ) hφ) • f : L2) :=
  rfl

end

end Torus
end SSU
