import SSU.Torus.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

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
  classical
  -- Expand the multiplier operators into `L^∞` scalar multiplication.
  simp [mulL2Op_apply, MeasureTheory.L2.inner_def]
  -- Reduce pointwise scalar multiplication to actual multiplication, a.e.
  have hsmul_f :
      ((toLinf (φ := φ) hφ) • f : L2) =ᵐ[μ] fun x : UC => ((toLinf (φ := φ) hφ) x) • (f x) := by
    simpa using (MeasureTheory.Lp.coeFn_lpSMul (f := (toLinf (φ := φ) hφ)) (g := f))
  have hsmul_g :
      ((toLinf (φ := ψ) hψ) • g : L2) =ᵐ[μ] fun x : UC => ((toLinf (φ := ψ) hψ) x) • (g x) := by
    simpa using (MeasureTheory.Lp.coeFn_lpSMul (f := (toLinf (φ := ψ) hψ)) (g := g))
  -- Use the a.e. pointwise formula for `inner` after rewriting the `smul` representatives.
  refine integral_congr_ae ?_
  filter_upwards [hsmul_f, hsmul_g] with x hxF hxG
  -- On complex numbers, `⟪a•u, b•v⟫ = star a * b * ⟪u,v⟫` and `⟪u,v⟫ = star u * v`.
  simp [hxF, hxG, inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm, mul_comm]

theorem inner_mulL2Op_eq_integral
    (φ ψ : UC → ℂ)
    (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (hψ : MemLp ψ (∞ : ℝ≥0∞) μ)
    (f g : L2) :
    inner ℂ (mulL2Op (φ := φ) hφ f) (mulL2Op (φ := ψ) hψ g)
      =
    ∫ x : UC, (star (φ x) * ψ x) * (star (f x) * g x) ∂μ := by
  classical
  -- Replace each `toLinf` evaluation by the underlying function a.e.
  have hφae : (fun x : UC => (toLinf (φ := φ) hφ) x) =ᵐ[μ] φ := by
    simpa [toLinf] using
      (hφ.coeFn_toLp (μ := μ) (p := (∞ : ℝ≥0∞)) (f := φ))
  have hψae : (fun x : UC => (toLinf (φ := ψ) hψ) x) =ᵐ[μ] ψ := by
    simpa [toLinf] using
      (hψ.coeFn_toLp (μ := μ) (p := (∞ : ℝ≥0∞)) (f := ψ))
  -- Start from the `toLinf` form and then apply `integral_congr_ae`.
  have h0 :=
    inner_mulL2Op_eq_integral_toLinf (φ := φ) (ψ := ψ) (hφ := hφ) (hψ := hψ) (f := f) (g := g)
  -- Rewrite the integrand a.e.
  -- We need to push the a.e. equalities through `star` and multiplication.
  have hint :
      (fun x : UC =>
          (star ((toLinf (φ := φ) hφ) x) * (toLinf (φ := ψ) hψ) x) * (star (f x) * g x))
        =ᵐ[μ]
      (fun x : UC => (star (φ x) * ψ x) * (star (f x) * g x)) := by
    -- Combine and simplify pointwise.
    filter_upwards [hφae, hψae] with x hxφ hxψ
    simp [hxφ, hxψ, mul_assoc, mul_left_comm, mul_comm]
  -- Finish.
  simpa using h0.trans (by
    -- Replace the integral by `integral_congr_ae` using `hint`.
    refine integral_congr_ae hint)

end

end Torus
end SSU

namespace SSU
namespace Torus

/-!
## Multiplier packet families (general extraction bridge)

This is a lightweight “public API” wrapper around `mulL2Op` + the Gram expansion lemma:
if a packet family is implemented as Fourier-side multipliers `(ψ i)`, then their Gram entries
are given by the corresponding weighted integral.
-/

open MeasureTheory

noncomputable section

namespace Packets

open scoped ENNReal

open SSU.Torus

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- A torus-side multiplier packet family: each packet is multiplication by `ψ i ∈ L^∞`. -/
structure MultiplierPacketFamily (ι : Type*) where
  ψ : ι → UC → ℂ
  memLp_ψ : ∀ i : ι, MemLp (ψ i) (∞ : ℝ≥0∞) μ

namespace MultiplierPacketFamily

variable {ι : Type*} (P : MultiplierPacketFamily ι)

/-- The bounded `L²` operator corresponding to packet `i`: multiplication by `ψ i`. -/
noncomputable def packetOp (i : ι) : L2 →L[ℂ] L2 :=
  mulL2Op (φ := P.ψ i) (P.memLp_ψ i)

@[simp] theorem packetOp_apply (i : ι) (f : L2) :
    P.packetOp i f = ((toLinf (φ := P.ψ i) (P.memLp_ψ i)) • f : L2) :=
  rfl

/-- Gram expansion for multiplier packets: `⟪T_i f, T_j g⟫` is the weighted integral of
`(ψ_i)^* ψ_j` against `(f)^* g`. -/
theorem inner_packetOp_eq_integral (i j : ι) (f g : L2) :
    inner ℂ (P.packetOp i f) (P.packetOp j g)
      =
    ∫ x : UC, (star (P.ψ i x) * P.ψ j x) * (star (f x) * g x) ∂μ := by
  simpa [MultiplierPacketFamily.packetOp] using
    (inner_mulL2Op_eq_integral
      (φ := P.ψ i) (ψ := P.ψ j) (hφ := P.memLp_ψ i) (hψ := P.memLp_ψ j) (f := f) (g := g))

end MultiplierPacketFamily

end Packets

end

end Torus
end SSU
