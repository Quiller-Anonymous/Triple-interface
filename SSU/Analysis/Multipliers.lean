import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

/-!
Generic (measure-space) multiplier operators on `L²`, and the associated Gram expansion.

This is the SSU “torus packet extraction bridge” in a domain-general form:
it does not depend on `AddCircle 1`, only on a measured space.

Downstream SSU components can instantiate this file with the torus Haar measure, but it is also
reusable in non-torus settings (e.g. `ℓ²(ℤ)` via counting measure, or other compact groups).
-/

namespace SSU
namespace Analysis

open scoped ENNReal

open MeasureTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- `L²` over a measure space `(α, μ)`. -/
abbrev L2 (μ : Measure α) := Lp ℂ (2 : ℝ≥0∞) μ

/-- `L^∞` over a measure space `(α, μ)`. -/
abbrev Linf (μ : Measure α) := Lp ℂ (∞ : ℝ≥0∞) μ

namespace Multipliers

variable {μ : Measure α} (φ : Linf (α := α) μ)

local notation "p∞" => (∞ : ℝ≥0∞)
local notation "p2" => (2 : ℝ≥0∞)

/-- Linear map `f ↦ φ • f` on `L²`. -/
noncomputable def mulL2ₗ : L2 (α := α) μ →ₗ[ℂ] L2 (α := α) μ where
  toFun f := (φ • f : L2 (α := α) μ)
  map_add' f g := by
    simpa using (MeasureTheory.Lp.add_smul (f := φ) (g₁ := f) (g₂ := g))
  map_smul' c f := by
    simpa using
      (MeasureTheory.Lp.smul_comm (μ := μ) (p := p∞) (q := p2) (r := p2)
          (c := c) (f := φ) (g := f)).symm

/-- Bounded linear operator `f ↦ φ • f` on `L²`. -/
noncomputable def mulL2 : L2 (α := α) μ →L[ℂ] L2 (α := α) μ :=
  LinearMap.mkContinuous (mulL2ₗ (φ := φ)) ‖φ‖ fun f => by
    have h :=
      (MeasureTheory.Lp.norm_smul_le (μ := μ) (p := p∞) (q := p2) (r := p2) (f := φ) (g := f))
    simpa using h

@[simp]
theorem mulL2_apply (f : L2 (α := α) μ) : mulL2 (φ := φ) f = (φ • f : L2 (α := α) μ) :=
  rfl

theorem norm_mulL2_apply_le (f : L2 (α := α) μ) :
    ‖mulL2 (φ := φ) f‖ ≤ ‖φ‖ * ‖f‖ := by
  simpa [mulL2_apply (φ := φ) (f := f)] using
    (MeasureTheory.Lp.norm_smul_le (μ := μ) (p := p∞) (q := p2) (r := p2) (f := φ) (g := f))

end Multipliers

variable {μ : Measure α}

/--
Pointwise `L^∞` class of a measurable essentially bounded function `φ`.

This is a thin wrapper around `MemLp.toLp`, named to make SSU's multiplier pipeline read cleanly.
-/
noncomputable def toLinf (φ : α → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ) : Linf (μ := μ) :=
  (hφ.toLp φ : Linf (α := α) μ)

/-- Multiplication operator on `L²` induced by `φ : α → ℂ` with `φ ∈ L^∞`. -/
noncomputable def mulL2Op (φ : α → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ) :
    L2 (α := α) μ →L[ℂ] L2 (α := α) μ :=
  Multipliers.mulL2 (μ := μ) (φ := (toLinf (μ := μ) (φ := φ) hφ))

@[simp]
theorem mulL2Op_apply (φ : α → ℂ) (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (f : L2 (α := α) μ) :
    mulL2Op (μ := μ) (φ := φ) hφ f =
      ((toLinf (μ := μ) (φ := φ) hφ) • f : L2 (α := α) μ) :=
  rfl

/-!
## Gram expansion (multiplier packets)

If `T_i` and `T_j` are multiplier operators, then `⟪T_i f, T_j g⟫` is an integral of the
pointwise multiplier product against `conj(f) * g`.
-/

theorem inner_mulL2Op_eq_integral_toLinf
    (φ ψ : α → ℂ)
    (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (hψ : MemLp ψ (∞ : ℝ≥0∞) μ)
    (f g : L2 (α := α) μ) :
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
      ((toLinf (μ := μ) (φ := φ) hφ) • f : L2 (α := α) μ)
        =ᵐ[μ] fun x : α => ((toLinf (μ := μ) (φ := φ) hφ) x) • (f x) := by
    simpa using (MeasureTheory.Lp.coeFn_lpSMul (f := (toLinf (μ := μ) (φ := φ) hφ)) (g := f))
  have hsmul_g :
      ((toLinf (μ := μ) (φ := ψ) hψ) • g : L2 (α := α) μ)
        =ᵐ[μ] fun x : α => ((toLinf (μ := μ) (φ := ψ) hψ) x) • (g x) := by
    simpa using (MeasureTheory.Lp.coeFn_lpSMul (f := (toLinf (μ := μ) (φ := ψ) hψ)) (g := g))
  -- Use the a.e. pointwise formula for `inner` after rewriting the `smul` representatives.
  refine integral_congr_ae ?_
  filter_upwards [hsmul_f, hsmul_g] with x hxF hxG
  simp [hxF, hxG, inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm, mul_comm]

theorem inner_mulL2Op_eq_integral
    (φ ψ : α → ℂ)
    (hφ : MemLp φ (∞ : ℝ≥0∞) μ) (hψ : MemLp ψ (∞ : ℝ≥0∞) μ)
    (f g : L2 (α := α) μ) :
    inner ℂ (mulL2Op (μ := μ) (φ := φ) hφ f) (mulL2Op (μ := μ) (φ := ψ) hψ g)
      =
    ∫ x : α, (star (φ x) * ψ x) * (star (f x) * g x) ∂μ := by
  classical
  have hφae : (fun x : α => (toLinf (μ := μ) (φ := φ) hφ) x) =ᵐ[μ] φ := by
    simpa [toLinf] using (hφ.coeFn_toLp (μ := μ) (p := (∞ : ℝ≥0∞)) (f := φ))
  have hψae : (fun x : α => (toLinf (μ := μ) (φ := ψ) hψ) x) =ᵐ[μ] ψ := by
    simpa [toLinf] using (hψ.coeFn_toLp (μ := μ) (p := (∞ : ℝ≥0∞)) (f := ψ))
  have h0 :=
    inner_mulL2Op_eq_integral_toLinf (μ := μ)
      (φ := φ) (ψ := ψ) (hφ := hφ) (hψ := hψ) (f := f) (g := g)
  have hint :
      (fun x : α =>
          (star ((toLinf (μ := μ) (φ := φ) hφ) x) * (toLinf (μ := μ) (φ := ψ) hψ) x) *
            (star (f x) * g x))
        =ᵐ[μ]
      (fun x : α => (star (φ x) * ψ x) * (star (f x) * g x)) := by
    filter_upwards [hφae, hψae] with x hxφ hxψ
    simp [hxφ, hxψ, mul_assoc, mul_left_comm, mul_comm]
  simpa using h0.trans (by
    refine integral_congr_ae hint)

/-!
## Multiplier packet families (domain-general extraction API)

This is the “public API” wrapper around `mulL2Op` + the Gram expansion lemma:
if a packet family is implemented as multiplier operators `(ψ i)`, then Gram entries are given by
the corresponding weighted integral.
-/

namespace Packets

/-- A multiplier packet family over `(α,μ)`: each packet is multiplication by `ψ i ∈ L^∞(μ)`. -/
structure MultiplierPacketFamily (μ : Measure α) (ι : Type*) where
  ψ : ι → α → ℂ
  memLp_ψ : ∀ i : ι, MemLp (ψ i) (∞ : ℝ≥0∞) μ

namespace MultiplierPacketFamily

variable {ι : Type*} {μ : Measure α} (P : MultiplierPacketFamily (α := α) μ ι)

/-- The bounded `L²` operator corresponding to packet `i`: multiplication by `ψ i`. -/
noncomputable def packetOp (i : ι) : L2 (α := α) μ →L[ℂ] L2 (α := α) μ :=
  mulL2Op (μ := μ) (φ := P.ψ i) (P.memLp_ψ i)

@[simp]
theorem packetOp_apply (i : ι) (f : L2 (α := α) μ) :
    P.packetOp i f =
      ((toLinf (μ := μ) (φ := P.ψ i) (P.memLp_ψ i)) • f : L2 (α := α) μ) :=
  rfl

/-- Gram expansion for multiplier packets. -/
theorem inner_packetOp_eq_integral (i j : ι) (f g : L2 (α := α) μ) :
    inner ℂ (P.packetOp i f) (P.packetOp j g)
      =
    ∫ x : α, (star (P.ψ i x) * P.ψ j x) * (star (f x) * g x) ∂μ := by
  simpa [MultiplierPacketFamily.packetOp] using
    (inner_mulL2Op_eq_integral (μ := μ)
      (φ := P.ψ i) (ψ := P.ψ j) (hφ := P.memLp_ψ i) (hψ := P.memLp_ψ j) (f := f) (g := g))

end MultiplierPacketFamily

end Packets

end

end Analysis
end SSU
