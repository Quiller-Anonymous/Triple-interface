import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

/-!
Generic `L²` multiplier operators.

This is a measure-space generic version of `SSU/Torus/Multipliers.lean`.

If `φ ∈ L^∞(μ)`, then pointwise multiplication `f ↦ φ • f` defines a bounded linear operator on
`L²(μ)`, and the corresponding Gram entry expands as an integral.
-/

namespace SSU
namespace Measure

open scoped ENNReal

open MeasureTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- `L²(μ)` on a general measure space. -/
abbrev L2 (μ : Measure α) := MeasureTheory.Lp (α := α) ℂ (2 : ℝ≥0∞) μ

/-- `L^∞(μ)` on a general measure space. -/
abbrev Linf (μ : Measure α) := MeasureTheory.Lp (α := α) ℂ (∞ : ℝ≥0∞) μ

local notation "p∞" => (∞ : ℝ≥0∞)
local notation "p2" => (2 : ℝ≥0∞)

namespace Multipliers

variable {μ : Measure α} (φ : Linf (μ := μ))

/-- Linear map `f ↦ φ • f` on `L²(μ)`. -/
noncomputable def mulL2ₗ : L2 (μ := μ) →ₗ[ℂ] L2 (μ := μ) where
  toFun f := (φ • f : L2 (μ := μ))
  map_add' f g := by
    simpa using (MeasureTheory.Lp.add_smul (f := φ) (g₁ := f) (g₂ := g))
  map_smul' c f := by
    simpa using
      (MeasureTheory.Lp.smul_comm (μ := μ) (p := p∞) (q := p2) (r := p2)
          (c := c) (f := φ) (g := f)).symm

/-- Bounded linear operator `f ↦ φ • f` on `L²(μ)`. -/
noncomputable def mulL2 : L2 (μ := μ) →L[ℂ] L2 (μ := μ) :=
  LinearMap.mkContinuous (mulL2ₗ (φ := φ)) ‖φ‖ fun f => by
    have h :=
      (MeasureTheory.Lp.norm_smul_le (μ := μ) (p := p∞) (q := p2) (r := p2) (f := φ) (g := f))
    simpa using h

@[simp]
theorem mulL2_apply (f : L2 (μ := μ)) : mulL2 (φ := φ) f = (φ • f : L2 (μ := μ)) :=
  rfl

end Multipliers

/--
Pointwise multiplier operator on `L²(μ)` from an `L^∞(μ)` function `φ`.

This is just `Multipliers.mulL2` applied to the `L^∞` class of `φ`.
-/
noncomputable def toLinf (μ : Measure α) (φ : α → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ) :
    Linf (μ := μ) :=
  (hφ.toLp φ : Linf (μ := μ))

/-- Multiplication operator on `L²(μ)` induced by a measurable bounded function `φ : α → ℂ`. -/
noncomputable def mulL2Op (μ : Measure α) (φ : α → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ) :
    L2 (μ := μ) →L[ℂ] L2 (μ := μ) :=
  Multipliers.mulL2 (φ := (toLinf (μ := μ) (φ := φ) hφ))

@[simp]
theorem mulL2Op_apply (μ : Measure α) (φ : α → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ)
    (f : L2 (μ := μ)) :
    mulL2Op (μ := μ) (φ := φ) hφ f =
      ((toLinf (μ := μ) (φ := φ) hφ) • f : L2 (μ := μ)) :=
  rfl

/-!
## Gram expansion

Deterministic lemma: if `T_i` and `T_j` are multiplier operators, then the Gram entry is the
integral of `conj(φ) * ψ * conj(f) * g`.
-/

theorem inner_mulL2Op_eq_integral_toLinf
    (μ : Measure α)
    (φ ψ : α → ℂ)
    (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (hψ : MemLp ψ (∞ : ℝ≥0∞) μ)
    (f g : L2 (μ := μ)) :
    inner ℂ (mulL2Op (μ := μ) (φ := φ) hφ f) (mulL2Op (μ := μ) (φ := ψ) hψ g)
      =
    ∫ x : α,
      (star ((toLinf (μ := μ) (φ := φ) hφ) x) * (toLinf (μ := μ) (φ := ψ) hψ) x)
        * (star (f x) * g x) ∂μ := by
  classical
  -- Expand the multiplier operators into `L^∞` scalar multiplication.
  simp [mulL2Op_apply, MeasureTheory.L2.inner_def]
  -- Reduce pointwise scalar multiplication to actual multiplication, a.e.
  have hsmul_f :
      ((toLinf (μ := μ) (φ := φ) hφ) • f : L2 (μ := μ)) =ᵐ[μ]
        fun x : α => ((toLinf (μ := μ) (φ := φ) hφ) x) • (f x) := by
    simpa using (MeasureTheory.Lp.coeFn_lpSMul (f := (toLinf (μ := μ) (φ := φ) hφ)) (g := f))
  have hsmul_g :
      ((toLinf (μ := μ) (φ := ψ) hψ) • g : L2 (μ := μ)) =ᵐ[μ]
        fun x : α => ((toLinf (μ := μ) (φ := ψ) hψ) x) • (g x) := by
    simpa using (MeasureTheory.Lp.coeFn_lpSMul (f := (toLinf (μ := μ) (φ := ψ) hψ)) (g := g))
  refine integral_congr_ae ?_
  filter_upwards [hsmul_f, hsmul_g] with x hxF hxG
  simp [hxF, hxG, inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm, mul_comm]

theorem inner_mulL2Op_eq_integral
    (μ : Measure α)
    (φ ψ : α → ℂ)
    (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (hψ : MemLp ψ (∞ : ℝ≥0∞) μ)
    (f g : L2 (μ := μ)) :
    inner ℂ (mulL2Op (μ := μ) (φ := φ) hφ f) (mulL2Op (μ := μ) (φ := ψ) hψ g)
      =
    ∫ x : α, (star (φ x) * ψ x) * (star (f x) * g x) ∂μ := by
  classical
  have hφae : (fun x : α => (toLinf (μ := μ) (φ := φ) hφ) x) =ᵐ[μ] φ := by
    simpa [toLinf] using (hφ.coeFn_toLp (μ := μ) (p := (∞ : ℝ≥0∞)) (f := φ))
  have hψae : (fun x : α => (toLinf (μ := μ) (φ := ψ) hψ) x) =ᵐ[μ] ψ := by
    simpa [toLinf] using (hψ.coeFn_toLp (μ := μ) (p := (∞ : ℝ≥0∞)) (f := ψ))
  have h0 :=
    inner_mulL2Op_eq_integral_toLinf (μ := μ) (φ := φ) (ψ := ψ) (hφ := hφ) (hψ := hψ) (f := f) (g := g)
  have hint :
      (fun x : α =>
          (star ((toLinf (μ := μ) (φ := φ) hφ) x) * (toLinf (μ := μ) (φ := ψ) hψ) x) *
            (star (f x) * g x))
        =ᵐ[μ]
      (fun x : α => (star (φ x) * ψ x) * (star (f x) * g x)) := by
    filter_upwards [hφae, hψae] with x hxφ hxψ
    simp [hxφ, hxψ]
  simpa using h0.trans (integral_congr_ae hint)

end

end Measure
end SSU
