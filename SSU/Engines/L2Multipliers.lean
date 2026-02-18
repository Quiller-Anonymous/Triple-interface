import SSU.Analysis.Multipliers

/-!
Generic `L²` multiplier operators.

This is a measure-space generic version of `SSU/Torus/Multipliers.lean`.

If `φ ∈ L^∞(μ)`, then pointwise multiplication `f ↦ φ • f` defines a bounded linear operator on
`L²(μ)`, and the corresponding Gram entry expands as an integral.
-/

namespace SSU
namespace Measure

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- `L²(μ)` on a general measure space. -/
abbrev L2 (μ : MeasureTheory.Measure α) := SSU.Analysis.L2 (α := α) μ

/-- `L^∞(μ)` on a general measure space. -/
abbrev Linf (μ : MeasureTheory.Measure α) := SSU.Analysis.Linf (α := α) μ

namespace Multipliers

variable {μ : MeasureTheory.Measure α} (φ : Linf (μ := μ))

/-- Linear map `f ↦ φ • f` on `L²(μ)`. -/
noncomputable abbrev mulL2ₗ : L2 (μ := μ) →ₗ[ℂ] L2 (μ := μ) :=
  SSU.Analysis.Multipliers.mulL2ₗ (μ := μ) (φ := φ)

/-- Bounded linear operator `f ↦ φ • f` on `L²(μ)`. -/
noncomputable abbrev mulL2 : L2 (μ := μ) →L[ℂ] L2 (μ := μ) :=
  SSU.Analysis.Multipliers.mulL2 (μ := μ) (φ := φ)

@[simp]
theorem mulL2_apply (f : L2 (μ := μ)) : mulL2 (φ := φ) f = (φ • f : L2 (μ := μ)) :=
  rfl

end Multipliers

/--
Pointwise multiplier operator on `L²(μ)` from an `L^∞(μ)` function `φ`.

This is just `Multipliers.mulL2` applied to the `L^∞` class of `φ`.
-/
noncomputable abbrev toLinf (μ : MeasureTheory.Measure α) (φ : α → ℂ)
    (hφ : MeasureTheory.MemLp φ (⊤ : ENNReal) μ) :
    Linf (μ := μ) :=
  SSU.Analysis.toLinf (μ := μ) (φ := φ) hφ

/-- Multiplication operator on `L²(μ)` induced by a measurable bounded function `φ : α → ℂ`. -/
noncomputable abbrev mulL2Op (μ : MeasureTheory.Measure α) (φ : α → ℂ)
    (hφ : MeasureTheory.MemLp φ (⊤ : ENNReal) μ) :
    L2 (μ := μ) →L[ℂ] L2 (μ := μ) :=
  SSU.Analysis.mulL2Op (μ := μ) (φ := φ) hφ

@[simp]
theorem mulL2Op_apply (μ : MeasureTheory.Measure α) (φ : α → ℂ)
    (hφ : MeasureTheory.MemLp φ (⊤ : ENNReal) μ)
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
    (μ : MeasureTheory.Measure α)
    (φ ψ : α → ℂ)
    (hφ : MeasureTheory.MemLp φ (⊤ : ENNReal) μ) (hψ : MeasureTheory.MemLp ψ (⊤ : ENNReal) μ)
    (f g : L2 (μ := μ)) :
    inner ℂ (mulL2Op (μ := μ) (φ := φ) hφ f) (mulL2Op (μ := μ) (φ := ψ) hψ g)
      =
    ∫ x : α,
      (star ((toLinf (μ := μ) (φ := φ) hφ) x) * (toLinf (μ := μ) (φ := ψ) hψ) x)
        * (star (f x) * g x) ∂μ := by
  simpa using
    (SSU.Analysis.inner_mulL2Op_eq_integral_toLinf (μ := μ)
      (φ := φ) (ψ := ψ) (hφ := hφ) (hψ := hψ) (f := f) (g := g))

theorem inner_mulL2Op_eq_integral
    (μ : MeasureTheory.Measure α)
    (φ ψ : α → ℂ)
    (hφ : MeasureTheory.MemLp φ (⊤ : ENNReal) μ) (hψ : MeasureTheory.MemLp ψ (⊤ : ENNReal) μ)
    (f g : L2 (μ := μ)) :
    inner ℂ (mulL2Op (μ := μ) (φ := φ) hφ f) (mulL2Op (μ := μ) (φ := ψ) hψ g)
      =
    ∫ x : α, (star (φ x) * ψ x) * (star (f x) * g x) ∂μ := by
  simpa using
    (SSU.Analysis.inner_mulL2Op_eq_integral (μ := μ)
      (φ := φ) (ψ := ψ) (hφ := hφ) (hψ := hψ) (f := f) (g := g))

end

end Measure
end SSU
