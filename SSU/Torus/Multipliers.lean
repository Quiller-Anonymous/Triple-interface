import SSU.Torus.Basic
import SSU.Analysis.Multipliers

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
abbrev L2 : Type := SSU.Analysis.L2 (α := UC) μ

/-- `L^∞` on the SSU torus `AddCircle 1`, with respect to Haar measure. -/
abbrev Linf : Type := SSU.Analysis.Linf (α := UC) μ

namespace Multipliers

variable (φ : Linf)

/-- Linear map `f ↦ φ • f` on `L²`. -/
noncomputable abbrev mulL2ₗ : L2 →ₗ[ℂ] L2 :=
  SSU.Analysis.Multipliers.mulL2ₗ (μ := μ) (φ := φ)

/-- Bounded linear operator `f ↦ φ • f` on `L²`. -/
noncomputable abbrev mulL2 : L2 →L[ℂ] L2 :=
  SSU.Analysis.Multipliers.mulL2 (μ := μ) (φ := φ)

@[simp]
theorem mulL2_apply (f : L2) : mulL2 (φ := φ) f = (φ • f : L2) :=
  rfl

theorem norm_mulL2_apply_le (f : L2) : ‖mulL2 (φ := φ) f‖ ≤ ‖φ‖ * ‖f‖ := by
  simpa [mulL2_apply (φ := φ) (f := f)] using
    (SSU.Analysis.Multipliers.norm_mulL2_apply_le (μ := μ) (φ := φ) (f := f))

end Multipliers

/--
Pointwise multiplier operator on `L²` from an `L^∞` function `φ`.

This is just `Multipliers.mulL2` applied to the `L^∞` class of `φ`.
-/
noncomputable abbrev toLinf (φ : UC → ℂ) (hφ : MeasureTheory.MemLp φ (∞ : ℝ≥0∞) μ) : Linf :=
  SSU.Analysis.toLinf (μ := μ) (φ := φ) hφ

/--
Multiplication operator on `L²` induced by a measurable bounded function `φ : UC → ℂ`.
-/
noncomputable abbrev mulL2Op (φ : UC → ℂ) (hφ : MeasureTheory.MemLp φ (∞ : ℝ≥0∞) μ) :
    L2 →L[ℂ] L2 :=
  SSU.Analysis.mulL2Op (μ := μ) (φ := φ) hφ

@[simp]
theorem mulL2Op_apply (φ : UC → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (f : L2) :
    mulL2Op (φ := φ) hφ f = ((toLinf (φ := φ) hφ) • f : L2) :=
  rfl

/-!
## Gram expansion for multiplier packets

This is the deterministic lemma used in the TeX “Gram expansion” step:

If `T_i` and `T_j` are Fourier-side multiplier operators, then
`⟪T_i f, T_j g⟫` is an integral of the pointwise multiplier product against `conj(f) * g`.
-/

theorem inner_mulL2Op_eq_integral_toLinf
    (φ ψ : UC → ℂ)
    (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (hψ : MemLp ψ (∞ : ℝ≥0∞) μ)
    (f g : L2) :
    inner ℂ (mulL2Op (φ := φ) hφ f) (mulL2Op (φ := ψ) hψ g)
      =
    ∫ x : UC,
      (star ((toLinf (φ := φ) hφ) x) * (toLinf (φ := ψ) hψ) x)
        * (star (f x) * g x) ∂μ := by
  simpa using
    (SSU.Analysis.inner_mulL2Op_eq_integral_toLinf (μ := μ)
      (φ := φ) (ψ := ψ) (hφ := hφ) (hψ := hψ) (f := f) (g := g))

theorem inner_mulL2Op_eq_integral
    (φ ψ : UC → ℂ)
    (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (hψ : MemLp ψ (∞ : ℝ≥0∞) μ)
    (f g : L2) :
    inner ℂ (mulL2Op (φ := φ) hφ f) (mulL2Op (φ := ψ) hψ g)
      =
    ∫ x : UC, (star (φ x) * ψ x) * (star (f x) * g x) ∂μ := by
  simpa using
    (SSU.Analysis.inner_mulL2Op_eq_integral (μ := μ)
      (φ := φ) (ψ := ψ) (hφ := hφ) (hψ := hψ) (f := f) (g := g))

end

end Torus
end SSU

namespace SSU
namespace Torus

/-!
## Multiplier packet families (torus instance)

Re-export the domain-general `SSU.Analysis.Packets.MultiplierPacketFamily` specialized to the
torus `(AddCircle 1, μ)`.
-/

noncomputable section

namespace Packets

open MeasureTheory

/-- Torus instance of `SSU.Analysis.Packets.MultiplierPacketFamily`. -/
abbrev MultiplierPacketFamily (ι : Type*) : Type _ :=
  SSU.Analysis.Packets.MultiplierPacketFamily (α := UC) μ ι

namespace MultiplierPacketFamily

variable {ι : Type*} (P : MultiplierPacketFamily ι)

/-- The multiplier operator corresponding to packet `i`: multiplication by `ψ i`. -/
noncomputable abbrev packetOp (i : ι) : L2 →L[ℂ] L2 :=
  SSU.Analysis.Packets.MultiplierPacketFamily.packetOp (P := P) i

@[simp]
theorem inner_packetOp_eq_integral (i j : ι) (f g : L2) :
    inner ℂ (P.packetOp i f) (P.packetOp j g)
      =
    ∫ x : UC, (star (P.ψ i x) * P.ψ j x) * (star (f x) * g x) ∂μ := by
  simpa [MultiplierPacketFamily.packetOp] using
    (SSU.Analysis.Packets.MultiplierPacketFamily.inner_packetOp_eq_integral (P := P) (i := i) (j := j)
      (f := f) (g := g))

end MultiplierPacketFamily

end Packets

end

end Torus
end SSU
