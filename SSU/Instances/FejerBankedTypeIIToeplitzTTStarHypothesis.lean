import SSU.Instances.FejerBankedTypeIIToeplitzKernel
import SSU.Engines.TypeIIProductToeplitzComplex

/-!
Fejér-banked packets: TT* / kernel-representation hypothesis (Toeplitz-in-product, complex kernel).

This file records the *next interface point* in the TeX-faithful Type–II → SSU pipeline.

With the user-chosen convention, we include packet overlap in the ξ-weight:

`w_{i,j}(ξ) := K̂_H(ξ) * ψ_i(ξ/X) * conj(ψ_j(ξ/X))`.

Deterministically, the weighted band integral of `|S(ξ)|²` Toeplitzizes into the TeX `k,k'` form
with the induced complex kernel `K_{i,j}(h)`.

What remains application-specific (and is hypothesized here) is the *TT* / reduction step that
identifies a concrete packet Gram entry with such a weighted band integral.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzTTStarHypothesis

open scoped BigOperators

noncomputable section

open MeasureTheory

variable {κ : Type*} [DecidableEq κ]

/--
Hypothesis: a packet Gram entry equals a TeX-style weighted band integral against the Type–II
product sum (real-frequency normalization).

This is the “TT* / kernel representation” step that turns a packet Gram into a Toeplitz-in-product
quadratic form.

It is intentionally stated without committing to how the Type–II coefficient array is extracted.
-/
structure Hypothesis where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2
  hH : 0 < Dpacket.H
  hX : Dpacket.X ≠ 0
  /-- TT* reduction target: packet Gram = weighted ξ-integral. -/
  inner_eq_weightedIntegral :
    ∀ f : SSU.Torus.L2, ∀ i ∈ Dpacket.J, ∀ j ∈ Dpacket.J,
      inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) f)
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) f)
        =
      (1 / Dpacket.X) *
        ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (Dtype.prodSumRealByProd Dpacket.X ξ f i j) *
              star (Dtype.prodSumRealByProd Dpacket.X ξ f i j)

/-!
## Fixed-signal (use-site) variant

When the application only needs the TT* identity for a single fixed signal `f`, we package that
case directly (mirroring the global hypothesis above).
-/

structure HypothesisFor where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2
  f : SSU.Torus.L2
  hH : 0 < Dpacket.H
  hX : Dpacket.X ≠ 0
  /-- TT* reduction target (fixed `f`): packet Gram = weighted ξ-integral. -/
  inner_eq_weightedIntegral :
    ∀ i ∈ Dpacket.J, ∀ j ∈ Dpacket.J,
      inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) f)
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) f)
        =
      (1 / Dpacket.X) *
        ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (Dtype.prodSumRealByProd Dpacket.X ξ f i j) *
              star (Dtype.prodSumRealByProd Dpacket.X ξ f i j)

namespace Hypothesis

variable (h : Hypothesis (κ := κ))

/--
Deterministic consequence: the Gram entry equals the TeX `k,k'` Toeplitz form
`ProductToeplitz.toeplitzFormTeXC` with the induced complex kernel `K_{i,j}`.
-/
theorem inner_eq_toeplitzFormTeXC
    (f : SSU.Torus.L2) (i : ℤ) (hi : i ∈ h.Dpacket.J) (j : ℤ) (hj : j ∈ h.Dpacket.J)
    :
    inner ℂ (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) f)
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) f)
      =
    (1 / h.Dpacket.X) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
            (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j t)
        (T := h.Dtype.tube)
        (F := h.Dtype.F f i j) := by
  classical
  -- Start from the TT* hypothesis.
  have h0 := h.inner_eq_weightedIntegral (f := f) (i := i) hi (j := j) hj
  -- Toeplitzize the weighted band integral deterministically.
  have hToeplitz :
      ((1 / h.Dpacket.X) *
        ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band h.Dpacket.H,
            (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j ξ) *
              (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j) *
                star (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j))
        =
      (1 / h.Dpacket.X) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j t)
          (T := h.Dtype.tube)
          (F := h.Dtype.F f i j) := by
    -- Apply deterministic Toeplitzization, then multiply by the scalar `(1/X)`.
    have hDet :=
      (SSU.Instances.FejerBankedTypeIIToeplitzKernel.integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC_auto
          (Dpacket := h.Dpacket) (D := h.Dtype) (X := h.Dpacket.X) (H := h.Dpacket.H)
          (f := f) (i := i) (j := j) (hH := h.hH) (hX := h.hX))
    -- Use an explicit `ℂ` scalar to avoid typeclass search ambiguities (`ℝ` vs `ℂ` multiplication).
    let c : ℂ := ((1 / h.Dpacket.X : ℝ) : ℂ)
    have := congrArg (fun z : ℂ => c * z) hDet
    simpa [c, mul_assoc] using this
  -- Chain the TT* hypothesis with the deterministic Toeplitzization.
  -- (Use `calc` to avoid definitional mismatches between `star` and `starRingEnd`.)
  calc
    inner ℂ (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) f)
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) f)
        =
      (1 / h.Dpacket.X) *
        ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band h.Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j ξ) *
            (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j) *
              star (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j) := by
              -- `h0` has `starRingEnd` in pretty-printing; `star` is definitional.
              simpa using h0
    _ =
      (1 / h.Dpacket.X) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j t)
          (T := h.Dtype.tube)
          (F := h.Dtype.F f i j) := hToeplitz

end Hypothesis

namespace HypothesisFor

variable (h : HypothesisFor (κ := κ))

/--
Deterministic consequence in the fixed-signal (`HypothesisFor`) setting:
the packet Gram entry equals the TeX `k,k'` Toeplitz form `ProductToeplitz.toeplitzFormTeXC`
with the induced complex kernel `K_{i,j}`.
-/
theorem inner_eq_toeplitzFormTeXC
    (i : ℤ) (hi : i ∈ h.Dpacket.J) (j : ℤ) (hj : j ∈ h.Dpacket.J) :
    inner ℂ (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) h.f)
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) h.f)
      =
    (1 / h.Dpacket.X) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
            (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j t)
        (T := h.Dtype.tube)
        (F := h.Dtype.F h.f i j) := by
  classical
  have h0 := h.inner_eq_weightedIntegral (i := i) hi (j := j) hj
  have hToeplitz :
      ((1 / h.Dpacket.X) *
        ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band h.Dpacket.H,
            (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j ξ) *
              (h.Dtype.prodSumRealByProd h.Dpacket.X ξ h.f i j) *
                star (h.Dtype.prodSumRealByProd h.Dpacket.X ξ h.f i j))
        =
      (1 / h.Dpacket.X) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j t)
          (T := h.Dtype.tube)
          (F := h.Dtype.F h.f i j) := by
    have hDet :=
      (SSU.Instances.FejerBankedTypeIIToeplitzKernel.integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC_auto
          (Dpacket := h.Dpacket) (D := h.Dtype) (X := h.Dpacket.X) (H := h.Dpacket.H)
          (f := h.f) (i := i) (j := j) (hH := h.hH) (hX := h.hX))
    let c : ℂ := ((1 / h.Dpacket.X : ℝ) : ℂ)
    have := congrArg (fun z : ℂ => c * z) hDet
    simpa [c, mul_assoc] using this
  calc
    inner ℂ (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) h.f)
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) h.f)
        =
      (1 / h.Dpacket.X) *
        ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band h.Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j ξ) *
            (h.Dtype.prodSumRealByProd h.Dpacket.X ξ h.f i j) *
              star (h.Dtype.prodSumRealByProd h.Dpacket.X ξ h.f i j) := by
              simpa using h0
    _ =
      (1 / h.Dpacket.X) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j t)
          (T := h.Dtype.tube)
          (F := h.Dtype.F h.f i j) := hToeplitz

end HypothesisFor

end

end FejerBankedTypeIIToeplitzTTStarHypothesis
end Instances
end SSU
