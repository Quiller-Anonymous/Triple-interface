import SSU.Engines.BGTypeIIArray
import SSU.Engines.BGTypeIIWeightedToeplitz

/-!
05_BG.tex — deterministic Toeplitzization of the *weighted* product exponential sum.

This is a thin specialization layer:

* `BGTypeIIArray.Data.prodSumRealByProd` is the TeX-normalized product exponential sum
  `S(ξ) = ∑_k A_k e(ξ k / X)` (finite sum over `tube.image prod`).
* `BGTypeIIWeightedToeplitz.integral_weight_mul_Ssum_mul_star_Ssum` Toeplitzizes
  `∫ w(ξ) |S(ξ)|^2 dξ` into a `k,k'` Toeplitz quadratic form with kernel
  `K_w(h) = ∫ w(ξ) e(ξ h / X) dξ`.

No SSU heart content and no application-specific input extraction occurs here.
-/

namespace SSU
namespace Engines
namespace BGTypeIIArrayWeightedToeplitz

open scoped BigOperators

noncomputable section

open MeasureTheory
open SSU.Engines.TypeII
open SSU.Engines.TypeII.ProductToeplitz

theorem integral_weight_mul_prodSumRealByProd_mul_star
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (D : SSU.Engines.BGTypeIIArray.Data H0)
    (X H : ℝ) (w : ℝ → ℂ) (f : H0) (i j : ℤ)
    (hH : 0 < H) (hw : IntegrableOn w (SSU.Engines.BGTypeIIWeightedToeplitz.band H))
    (hX : X ≠ 0) :
    (∫ ξ in SSU.Engines.BGTypeIIWeightedToeplitz.band H,
        w ξ * (D.prodSumRealByProd X ξ f i j) * star (D.prodSumRealByProd X ξ f i j))
      =
    ∑ k ∈ (D.tube).image prod, ∑ k' ∈ (D.tube).image prod,
      (D.A f i j k') * star (D.A f i j k) *
        (SSU.Engines.BGTypeIIWeightedToeplitz.K X H w (k' - k)) := by
  classical
  -- This is exactly `BGTypeIIWeightedToeplitz.integral_weight_mul_Ssum_mul_star_Ssum`,
  -- after unfolding `prodSumRealByProd` as a finite `k`-sum.
  simpa [SSU.Engines.BGTypeIIArray.Data.prodSumRealByProd,
    SSU.Engines.BGTypeIIWeightedToeplitz.Ssum,
    SSU.Engines.BGTypeIIArray.Data.A] using
    (SSU.Engines.BGTypeIIWeightedToeplitz.integral_weight_mul_Ssum_mul_star_Ssum
      (X := X) (H := H) (w := w) (S := (D.tube).image prod) (A := fun k => D.A f i j k)
      hH hw hX)

/--
Same as `integral_weight_mul_prodSumRealByProd_mul_star`, but with the TeX sum expressed as a
torus character sum evaluated at `x = (ξ/X) : 𝕋`.

This is the deterministic bridge used when an application’s “signal” naturally lives on the torus.
-/
theorem integral_weight_mul_prodSumTorusByProd_mul_star
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (D : SSU.Engines.BGTypeIIArray.Data H0)
    (X H : ℝ) (w : ℝ → ℂ) (f : H0) (i j : ℤ)
    (hH : 0 < H) (hw : IntegrableOn w (SSU.Engines.BGTypeIIWeightedToeplitz.band H))
    (hX : X ≠ 0) :
    (∫ ξ in SSU.Engines.BGTypeIIWeightedToeplitz.band H,
        w ξ *
          (D.prodSumTorusByProd f i j ((ξ / X : ℝ) : SSU.Torus.UC)) *
            star (D.prodSumTorusByProd f i j ((ξ / X : ℝ) : SSU.Torus.UC)))
      =
    ∑ k ∈ (D.tube).image prod, ∑ k' ∈ (D.tube).image prod,
      (D.A f i j k') * star (D.A f i j k) *
        (SSU.Engines.BGTypeIIWeightedToeplitz.K X H w (k' - k)) := by
  classical
  -- Convert the torus-side product sum to the real-frequency form pointwise, then reuse the
  -- already-proved Toeplitzization lemma.
  have hbridge :
      ∀ ξ : ℝ, D.prodSumRealByProd X ξ f i j =
        D.prodSumTorusByProd f i j ((ξ / X : ℝ) : SSU.Torus.UC) := by
    intro ξ
    simpa using
      (D.prodSumRealByProd_eq_prodSumTorusByProd (X := X) (ξ := ξ) (f := f) (i := i) (j := j))
  -- The RHS is already in terms of `A_k`, so only the LHS needs rewriting.
  have htoeplitz :=
    integral_weight_mul_prodSumRealByProd_mul_star
      (D := D) (X := X) (H := H) (w := w) (f := f) (i := i) (j := j) hH hw hX
  simpa [hbridge] using htoeplitz

end

end BGTypeIIArrayWeightedToeplitz
end Engines
end SSU
