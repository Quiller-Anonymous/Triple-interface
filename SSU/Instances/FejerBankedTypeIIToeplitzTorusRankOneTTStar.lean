import SSU.Instances.FejerBankedTypeIIToeplitzKernel
import SSU.Engines.BGTypeIIRankOne
import SSU.Engines.BGTypeIIRankOneSignal
import SSU.Engines.BGTypeIIWeightedToeplitz
import SSU.Engines.TypeIIProductToeplitzComplex

/-!
Deterministic Toeplitzization for the rank-one Type–II signal, in TeX normalization.

This file *does not* attempt to build torus-side packet operators. Instead, it isolates the
deterministic “Toeplitz kernel extraction” step that turns the band integral

`∫_{|ξ|≤1/H} w_{i,j}(ξ) |S(ξ)|² dξ`

into the TeX `k,k'` quadratic form

`∑_{k,k'} A_{k'} * conj(A_k) * K_{i,j}(k' - k)`.

The outer SSU pipeline (TT* on the short-shift kernel, the substitution `x = ξ/X` with Jacobian
`1/X`, and the extraction of the Type–II rank-one signal from packets) is handled in other files.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzTorusRankOneTTStar

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory

variable {κ : Type*} [DecidableEq κ]

namespace RankOne

open SSU.Engines.BGTypeIIRankOne
open SSU.Engines.BGTypeIIRankOne.Input
open SSU.Engines.BGTypeIIWeightedToeplitz
open SSU.Engines.TypeII
open SSU.Engines.TypeII.ProductToeplitz
open SSU.Instances.FejerBankedTypeIIToeplitzKernel

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : SSU.Engines.BGTypeIIRankOne.Input)

set_option maxHeartbeats 1000000

theorem bandIntegral_eq_toeplitzFormTeXC_rankOne
    (hH : 0 < D.H) (hX : D.X ≠ 0) (i j : ℤ) :
    (∫ ξ in Weight.band D.H,
        (Weight.wLean (D := D) D.X D.H i j ξ) *
          (I.signalRealByProd P W D.X ξ) *
            star (I.signalRealByProd P W D.X ξ))
      =
    SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
      (K := fun t => Weight.KLean (D := D) D.X D.H i j t)
      (T := P.box)
      (F := fun p => I.F (P := P) (W := W) p) := by
  classical
  -- Toeplitzize the weighted band integral for `S(ξ) = ∑_k A_k e(ξ k / X)`.
  have hw :
      IntegrableOn (fun ξ => Weight.wLean (D := D) D.X D.H i j ξ) (Weight.band D.H) :=
    Weight.integrableOn_wLean (D := D) (X := D.X) (H := D.H) hH i j
  have hToeplitz :=
    (SSU.Engines.BGTypeIIWeightedToeplitz.integral_weight_mul_Ssum_mul_star_Ssum
      (X := D.X) (H := D.H)
      (w := fun ξ => Weight.wLean (D := D) D.X D.H i j ξ)
      (S := P.box.image prod) (A := fun k => I.A (P := P) (W := W) k)
      (hH := hH) (hw := hw) (hX := hX))
  -- Rewrite `Ssum` as the TeX rank-one signal, then match the RHS to `toeplitzFormTeXC`.
  -- `toeplitzFormTeXC` uses `coeffByProd P.box (I.F P W)`, which is definitionally `I.A P W`.
  -- The extracted kernel is definitionally `Weight.KLean`.
  simpa [SSU.Engines.BGTypeIIWeightedToeplitz.Ssum, SSU.Engines.BGTypeIIWeightedToeplitz.K,
    SSU.Engines.BGTypeIIWeightedToeplitz.band, Weight.band, Weight.KLean,
    SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC, SSU.Engines.BGTypeIIRankOne.Input.A,
    SSU.Engines.BGTypeIIRankOneSignal.Input.signalRealByProd, SSU.Engines.BGTypeIIRankOneSignal.Input.signalTorusByProd,
    SSU.Engines.BGTypeIIRankOneSignal.Input.e_eq_fourier_coe, SSU.Engines.BGTypeIIRankOne.Input.F,
    SSU.Engines.BGTypeIIRankOne.Input.W_on_point] using hToeplitz

/--
Same lemma, but expressed using the generic `BGTypeIIArray.Data` packaging of the rank-one
coefficient array on the full dyadic box.

This is the normalization needed to plug the result directly into the later TT* interfaces that
expect a `BGTypeIIArray.Data` object.
-/
theorem bandIntegral_eq_toeplitzFormTeXC_rankOne_boxData
    (hU : 2 * P.N ≤ P.U)
    (hH : 0 < D.H) (hX : D.X ≠ 0) (i j : ℤ) :
    (∫ ξ in Weight.band D.H,
        (Weight.wLean (D := D) D.X D.H i j ξ) *
          (I.signalRealByProd P W D.X ξ) *
            star (I.signalRealByProd P W D.X ξ))
      =
    SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
      (K := fun t => Weight.KLean (D := D) D.X D.H i j t)
      (T := (I.boxData (P := P) hU W).tube)
      (F := (I.boxData (P := P) hU W).F (0 : SSU.Torus.L2) i j) := by
  classical
  -- Start from the original statement.
  have hmain :=
    bandIntegral_eq_toeplitzFormTeXC_rankOne (D := D) (P := P) (W := W) (I := I) hH hX i j
  -- Rewrite the tube finset and coefficient array using the deterministic `boxData` lemmas.
  have htube : (I.boxData (P := P) hU W).tube = P.box :=
    I.boxData_tube_eq_box (P := P) (hU := hU) (W := W)
  have hF :
      (I.boxData (P := P) hU W).F (0 : SSU.Torus.L2) i j = fun p => I.F (P := P) (W := W) p := by
    funext p
    simpa using (I.boxData_F_eq_F (P := P) (hU := hU) (W := W) (f := (0 : SSU.Torus.L2)) (i := i) (j := j) (p := p))
  simpa [htube, hF] using hmain

/--
Same deterministic Toeplitzization, but stated with the **double-sum** real-frequency signal
`∑_{(d,n)∈box} α_d β_n W(d/D,n/N) e(ξ d n / X)` (TeX’s preferred presentation).
-/
theorem bandIntegral_eq_toeplitzFormTeXC_rankOne_DN
    (hH : 0 < D.H) (hX : D.X ≠ 0) (i j : ℤ) :
    (∫ ξ in Weight.band D.H,
        (Weight.wLean (D := D) D.X D.H i j ξ) *
          (I.signalRealDN P W D.X ξ) *
            star (I.signalRealDN P W D.X ξ))
      =
    SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
      (K := fun t => Weight.KLean (D := D) D.X D.H i j t)
      (T := P.box)
      (F := fun p => I.F (P := P) (W := W) p) := by
  classical
  -- Rewrite `signalRealDN` into the grouped-by-product form and reuse the proved lemma.
  have hmain :=
    bandIntegral_eq_toeplitzFormTeXC_rankOne (D := D) (P := P) (W := W) (I := I) hH hX i j
  -- `signalRealDN = signalRealByProd` deterministically, so the integrals agree.
  simpa [SSU.Engines.BGTypeIIRankOne.Input.signalRealDN_eq_signalRealByProd] using hmain

end RankOne

end
end FejerBankedTypeIIToeplitzTorusRankOneTTStar
end Instances
end SSU
