import SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis

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

end

end FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis
end Instances
end SSU

