import SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof

/-!
Rank-one (Type–II) Toeplitz reduction for Fejér-banked packets (proved, TeX-faithful).

Scope: **rank-one signals only**.

This file provides the first “real” (non-toy) `inner = Toeplitz` statement in the Type–II pipeline,
specialized to the TeX rank-one coefficient array `F(d,n) = α_d β_n W(d/D,n/N)` on the dyadic box.

It is a thin re-export of the proved milestone in
`SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean`, but with an API-level filename that
matches the TeX narrative (“Toeplitz reduction, rank-one input”).
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzReductionRankOne

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus

variable {κ : Type*} [DecidableEq κ]

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : SSU.Engines.BGTypeIIRankOne.Input)

/-!
## Main lemma (rank-one input)

The packet operators here are the *real-frequency TT\** model packets from
`FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp`:

`f(ξ) ↦ ( (√K̂_H(ξ)) * ψ_j((ξ/X):𝕋) ) * f(ξ)` on the ξ-band with TeX-normalized measure `(1/X)dξ`.

The input signal is the TeX rank-one Type–II product exponential sum `S(ξ) = ∑_k A_k e(ξk/X)`.
The conclusion is the TeX `k,k'` Toeplitz quadratic form with induced kernel `K_{i,j}`.
-/

theorem inner_eq_toeplitzFormTeXC_rankOne
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H)
    (i j : ℤ) :
    let Dtype :
        SSU.Engines.BGTypeIIArray.Data
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.L2Band D.X D.H) :=
      SSU.Engines.BGTypeIIArray.Data.mkBox
        (H := SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.L2Band D.X D.H)
        P hU W.toWeight
        (α := fun _f _i _j d => I.α d)
        (β := fun _f _i _j n => I.β n)
    inner ℂ
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S
            (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S
            (D := D) (I := I) (P := P) (W := W) D.X D.H))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := Dtype.tube)
        (F := Dtype.F
          (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S
            (D := D) (I := I) (P := P) (W := W) D.X D.H) i j) := by
  simpa using
    (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.inner_eq_toeplitzFormTeXC_rankOne_mkBoxData
      (D := D) (P := P) (W := W) (I := I) (hU := hU) (hX := hX) (hH := hH) (i := i) (j := j))

end

end FejerBankedTypeIIToeplitzReductionRankOne
end Instances
end SSU

