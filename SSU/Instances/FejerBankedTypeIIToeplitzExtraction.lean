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
  -- Rewrite the torus-side product sum as the real-frequency TeX `e(ξk/X)` sum, then apply the
  -- deterministic Toeplitzization lemma with the packet-overlap weight.
  have hbridge :
      ∀ ξ : ℝ, D.prodSumRealByProd X ξ f i j =
        D.prodSumTorusByProd f i j ((ξ / X : ℝ) : SSU.Torus.UC) := by
    intro ξ
    simpa using (D.prodSumRealByProd_eq_prodSumTorusByProd (X := X) (ξ := ξ) (f := f) (i := i) (j := j))
  -- Apply the already-proved weighted Toeplitzization for `prodSumRealByProd`.
  have htoeplitz :=
    (SSU.Instances.FejerBankedTypeIIToeplitzKernel.integral_weight_mul_prodSumRealByProd_mul_star_auto
      (Dpacket := Dpacket) (D := D) (X := X) (H := H) (f := f) (i := i) (j := j)
      (hH := hH) (hX := hX))
  -- Use `hbridge` to rewrite the LHS integrand.
  -- (The RHS already matches by definition of `Weight.K`.)
  simpa [hbridge] using htoeplitz

end

end FejerBankedTypeIIToeplitzExtraction
end Instances
end SSU
