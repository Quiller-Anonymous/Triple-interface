import SSU.Instances.FejerBankedTypeIIToeplitzKernel
import SSU.Engines.BGTypeIIArray

/-!
Fejér-banked packets: deterministic “Type–II signal → Toeplitz form” extraction.

This file proves the first non-toy *deterministic* reduction lemma in the TeX Toeplitz Type–II
pipeline:

* start from a Type–II coefficient array on a tube (or dyadic box) and its aggregated coefficients
  `A_k` (05_BG.tex Eq. (5.2));
* form the TeX real-frequency product exponential sum `S(ξ) = ∑_k A_k e(ξ k / X)`; and
* Toeplitzize the *weighted* band integral
    `∫_{|ξ|≤1/H} w_{i,j}(ξ) |S(ξ)|^2 dξ`
  into the `k,k'` Toeplitz quadratic form with kernel
    `K_{i,j}(h) := ∫ w_{i,j}(ξ) e(ξ h / X) dξ`.

Here `w_{i,j}` is the TeX-faithful packet-overlap weight
`K̂_H(ξ) * ψ_i(ξ/X) * conj(ψ_j(ξ/X))` from `FejerBankedTypeIIToeplitzKernel`.

This lemma does *not* assert that a concrete packet Gram equals such a band integral; that is the
application-specific TT*/reindexing step.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzExtraction

open scoped BigOperators

noncomputable section

open MeasureTheory
open SSU.Engines.TypeII.ProductToeplitz

variable {κ : Type*} [DecidableEq κ]

theorem integral_weight_mul_prodSumTorusByProd_mul_star
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (D : SSU.Engines.BGTypeIIArray.Data H0)
    (X H : ℝ) (f : H0) (i j : ℤ)
    (hH : 0 < H)
    (hX : X ≠ 0) :
    (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band H,
        (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean (D := Dpacket) X H i j ξ) *
          (D.prodSumTorusByProd f i j ((ξ / X : ℝ) : SSU.Torus.UC)) *
            star (D.prodSumTorusByProd f i j ((ξ / X : ℝ) : SSU.Torus.UC)))
      =
    ∑ k ∈ (D.tube).image prod, ∑ k' ∈ (D.tube).image prod,
      (D.A f i j k') * star (D.A f i j k) *
        (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := Dpacket) X H i j (k' - k)) := by
  classical
  -- This is the domain-general Toeplitzization lemma, specialized to the Fejér-banked weight.
  -- (The `KLean` on the RHS is definitional `BGTypeIIWeightedToeplitz.K` applied to `wLean`.)
  simpa [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean,
    SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band]
    using
      (SSU.Engines.BGTypeIIArrayWeightedToeplitz.integral_weight_mul_prodSumTorusByProd_mul_star
        (D := D) (X := X) (H := H)
        (w := fun ξ => SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean (D := Dpacket) X H i j ξ)
        (f := f) (i := i) (j := j) (hH := hH)
        (hw := by
          -- Integrability of the Fejér-banked weight is already packaged.
          simpa [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band] using
            (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.integrableOn_wLean
              (D := Dpacket) (X := X) (H := H) hH i j))
        (hX := hX))

end

end FejerBankedTypeIIToeplitzExtraction
end Instances
end SSU
