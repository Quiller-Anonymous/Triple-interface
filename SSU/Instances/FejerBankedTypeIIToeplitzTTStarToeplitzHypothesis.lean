import SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis
import SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets

/-!
Fejér-banked packets: TT* interface stated on the **physical-side Toeplitz form**.

TeX (05_BG / 05b_SSU) narrates the reduction as:

1. identify a Gram entry with a *short-shift Toeplitz quadratic form*;
2. Fourier-expand the short-shift kernel `K_H` and swap sums/integrals to introduce `K̂_H`.

In this repo, Step 2 is proved deterministically (see
`SSU.Instances.FejerBankedTypeIIToeplitzKernel.integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC_auto`).

So this file provides an equivalent interface point where the TT* reduction is stated directly as

`inner = (1/X) * toeplitzFormTeXC (K_{i,j})`,

and then derives the existing “weighted ξ-band integral” hypothesis as a corollary.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis

open scoped BigOperators

noncomputable section

open MeasureTheory

variable {κ : Type*} [DecidableEq κ]

/--
Toeplitz-form TT* hypothesis (TeX-facing):

For each packet pair `(i,j)`, the Gram entry equals a Toeplitz-in-product quadratic form with the
induced complex kernel `K_{i,j}` (already integrating the packet overlap factor).

This is equivalent to the ξ-band TT* hypothesis, since Toeplitzization of the ξ-band integral is
deterministic.
-/
structure Hypothesis where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2
  hH : 0 < Dpacket.H
  hX : Dpacket.X ≠ 0
  /-- TT* reduction target: packet Gram = Toeplitz form. -/
  inner_eq_toeplitzFormTeXC :
    ∀ f : SSU.Torus.L2, ∀ i ∈ Dpacket.J, ∀ j ∈ Dpacket.J,
      inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) f)
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) f)
        =
      (1 / Dpacket.X) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := Dtype.tube)
          (F := Dtype.F f i j)

/-!
## Fixed-signal (use-site) variant

For some applications (e.g. rank-one extractions), we only need the TT* Toeplitz identity for a
single fixed input signal `f`. This lighter interface packages that case directly.
-/

structure HypothesisFor where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2
  f : SSU.Torus.L2
  hH : 0 < Dpacket.H
  hX : Dpacket.X ≠ 0
  /-- TT* reduction target (fixed `f`): packet Gram = Toeplitz form. -/
  inner_eq_toeplitzFormTeXC :
    ∀ i ∈ Dpacket.J, ∀ j ∈ Dpacket.J,
      inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) f)
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) f)
        =
      (1 / Dpacket.X) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := Dtype.tube)
          (F := Dtype.F f i j)

/-!
## Pair-dependent extracted-signal variant

The proved non-toy frozen-packet extraction has the honest TT* shape

`signal(f,i,j) : L²(𝕋)`,

so the torus-side signal depends on the packet pair `(i,j)`. This does not fit the older
`Hypothesis` / `HypothesisFor` interfaces, where the same torus signal is reused across all packet
pairs. This structure isolates the honest Step-2 statement without forcing it into a false
operator-global shape.
-/

structure PairHypothesis
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data H0
  hH : 0 < Dpacket.H
  hX : 0 < Dpacket.X
  hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)
  signal : H0 → ℤ → ℤ → SSU.Torus.L2
  /-- Pair-dependent TT* reduction target: packet Gram = Toeplitz form. -/
  inner_eq_toeplitzFormTeXC :
    ∀ f : H0, ∀ i ∈ Dpacket.J, ∀ j ∈ Dpacket.J,
      inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (signal f i j))
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (signal f i j))
        =
      (((1 / Dpacket.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := Dtype.tube)
          (F := Dtype.F f i j))

namespace PairHypothesis

variable {κ : Type*} [DecidableEq κ]
variable {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]

variable (h : PairHypothesis (κ := κ) H0)

/-- The pair-dependent Toeplitz-form TT* identity, restated as a namespace method. -/
theorem inner_eq_toeplitzFormTeXC_onJ
    (f : H0) (i : ℤ) (hi : i ∈ h.Dpacket.J) (j : ℤ) (hj : j ∈ h.Dpacket.J) :
    inner ℂ (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) (h.signal f i j))
        (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) (h.signal f i j))
      =
    (((1 / h.Dpacket.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
            (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j t)
        (T := h.Dtype.tube)
        (F := h.Dtype.F f i j)) :=
  h.inner_eq_toeplitzFormTeXC (f := f) (i := i) hi (j := j) hj

/-- Canonical non-toy Step-2 package for the frozen Fejér-banked packet family. -/
noncomputable def ofFrozenPackets
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (hH : 0 < Dpacket.H)
    (hX : 0 < Dpacket.X)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)) :
    PairHypothesis (κ := κ) H0 where
  Dpacket := Dpacket
  Dtype := Dtype
  hH := hH
  hX := hX
  hsmall := hsmall
  signal := fun f i j =>
    SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
      (Dpacket := Dpacket) (D := Dtype) f i j hH
  inner_eq_toeplitzFormTeXC := by
    intro f i hi j hj
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.inner_packetOpUnnormalized_eq_toeplitzFormTeXC_onJ
        (Dpacket := Dpacket) (D := Dtype) (f := f)
        (i := i) hi (j := j) hj
        (hX := hX) (hH := hH) (hsmall := hsmall))

end PairHypothesis

namespace Hypothesis

variable (h : Hypothesis (κ := κ))

/--
Convert a Toeplitz-form TT* hypothesis into the ξ-band weighted-integral TT* hypothesis.

This is the TeX “Fourier-expand the kernel and swap sums/integrals” step, but it is proved
deterministically in the kernel-extraction file.
-/
noncomputable def toBandHypothesis :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis.Hypothesis (κ := κ) where
  Dpacket := h.Dpacket
  Dtype := h.Dtype
  hH := h.hH
  hX := h.hX
  inner_eq_weightedIntegral := by
    classical
    intro f i hi j hj
    -- Start from the Toeplitz-form TT* hypothesis.
    have hToeplitz := h.inner_eq_toeplitzFormTeXC (f := f) (i := i) hi (j := j) hj
    -- Deterministically rewrite the Toeplitz form as a weighted ξ-band integral.
    have hDet :=
      (SSU.Instances.FejerBankedTypeIIToeplitzKernel.integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC_auto
        (Dpacket := h.Dpacket) (D := h.Dtype) (X := h.Dpacket.X) (H := h.Dpacket.H)
        (f := f) (i := i) (j := j) (hH := h.hH) (hX := h.hX))
    -- Replace the Toeplitz form using `hDet`.
    -- (We keep the outer `1/X` prefactor, matching TeX normalization.)
    simpa [mul_assoc] using hToeplitz.trans (by
      -- `hDet` has the integral on the LHS; we want to rewrite the RHS of `hToeplitz`.
      -- Turn `hDet` around and multiply by `1/X`.
      have := congrArg (fun z : ℂ => ((1 / h.Dpacket.X : ℝ) : ℂ) * z) hDet.symm
      simpa [mul_assoc] using this)

end Hypothesis

namespace HypothesisFor

variable (h : HypothesisFor (κ := κ))

noncomputable def toBandHypothesis :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis.HypothesisFor (κ := κ) where
  Dpacket := h.Dpacket
  Dtype := h.Dtype
  f := h.f
  hH := h.hH
  hX := h.hX
  inner_eq_weightedIntegral := by
    classical
    intro i hi j hj
    -- Start from the Toeplitz-form TT* hypothesis.
    have hToeplitz := h.inner_eq_toeplitzFormTeXC (i := i) hi (j := j) hj
    -- Deterministically rewrite the Toeplitz form as a weighted ξ-band integral.
    have hDet :=
      (SSU.Instances.FejerBankedTypeIIToeplitzKernel.integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC_auto
        (Dpacket := h.Dpacket) (D := h.Dtype) (X := h.Dpacket.X) (H := h.Dpacket.H)
        (f := h.f) (i := i) (j := j) (hH := h.hH) (hX := h.hX))
    -- Replace the Toeplitz form using `hDet`, keeping the `1/X` prefactor.
    simpa [mul_assoc] using hToeplitz.trans (by
      have := congrArg (fun z : ℂ => ((1 / h.Dpacket.X : ℝ) : ℂ) * z) hDet.symm
      simpa [mul_assoc] using this)

end HypothesisFor

namespace SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis.HypothesisFor

variable {κ : Type*} [DecidableEq κ]

/--
Upgrade a fixed-signal weighted-band TT* hypothesis to the fixed-signal Toeplitz-form TT* hypothesis.

This is the deterministic “Toeplitzize the ξ-band integral” direction in the use-site setting.
-/
noncomputable def toToeplitzHypothesis
    (h : SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis.HypothesisFor (κ := κ)) :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.HypothesisFor (κ := κ) where
  Dpacket := h.Dpacket
  Dtype := h.Dtype
  f := h.f
  hH := h.hH
  hX := h.hX
  inner_eq_toeplitzFormTeXC := by
    intro i hi j hj
    simpa using h.inner_eq_toeplitzFormTeXC (i := i) hi (j := j) hj

end SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis.HypothesisFor

end

end FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis
end Instances
end SSU
