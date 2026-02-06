import SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal

/-!
Fejér-banked packets: proved **arc-form TT*** identity (TeX-faithful).

This file is intentionally a thin wrapper.

The initial attempt to prove the torus-side arc identity by constructing a weighted torus `L²`
signal `g(x) := 1_arc(x) * √(KhatTorus(X,H)(x)) * S(x)` directly ran into avoidable measurability
and `MemLp` bookkeeping.

For the SSU pipeline, the TeX order is:

1. work in the real-frequency band model on `[-1/H, 1/H]` with the TeX-normalized measure
   `(1/X) dξ` (TT* step),
2. then deterministically rewrite the band integral as an *arc-evaluated torus integral*
   (no wrap-around, `x = ξ/X`), producing the arc-form TT* integrand.

That is already proved in
`SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean` as
`inner_eq_arcIntegral_rankOne`. We re-export it here so that downstream “SSU heart” code can
depend on a file whose name matches the TeX narrative (“arc proof”).
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzTTStarArcProof

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus

variable {κ : Type*} [DecidableEq κ]

open SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : SSU.Engines.BGTypeIIRankOne.Input)

/-- Re-export of the proved TeX Toeplitz Type–II reduction for the rank-one Type–II signal. -/
theorem inner_eq_toeplitzFormTeXC_rankOne
    (hX : 0 < D.X) (hH : 0 < D.H)
    (i j : ℤ) :
    inner ℂ
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := P.box)
        (F := fun p => I.F (P := P) (W := W) p) := by
  simpa using
    (FejerBankedTypeIIToeplitzRankOneReal.inner_eq_toeplitzFormTeXC_rankOne
      (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (i := i) (j := j))

/-- Same as `inner_eq_toeplitzFormTeXC_rankOne`, but with `i,j ∈ D.J` arguments (fits “SSU heart” APIs). -/
theorem inner_eq_toeplitzFormTeXC_rankOne_onJ
    (hX : 0 < D.X) (hH : 0 < D.H)
    (i : ℤ) (_hi : i ∈ D.J) (j : ℤ) (_hj : j ∈ D.J) :
    inner ℂ
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := P.box)
        (F := fun p => I.F (P := P) (W := W) p) := by
  simpa using inner_eq_toeplitzFormTeXC_rankOne (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) i j

/-- Re-export of the proved TeX arc-form TT* identity for the rank-one Type–II signal. -/
theorem inner_eq_arcIntegral_rankOne
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i j : ℤ) :
    inner ℂ
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
      =
    ∫ z : UC,
      (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand D.X D.H).indicator
        (fun x =>
          (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus D.X D.H x : ℝ) : ℂ) *
              star (D.ψ i x) * (D.ψ j x)) *
            (I.signalTorusByProd P W x) *
              star (I.signalTorusByProd P W x))
        z := by
  simpa using
    (FejerBankedTypeIIToeplitzRankOneReal.inner_eq_arcIntegral_rankOne
      (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (hsmall := hsmall) (i := i) (j := j))

/-- Same as `inner_eq_arcIntegral_rankOne`, but with `i,j ∈ D.J` arguments (fits “SSU heart” APIs). -/
theorem inner_eq_arcIntegral_rankOne_onJ
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i : ℤ) (_hi : i ∈ D.J) (j : ℤ) (_hj : j ∈ D.J) :
    inner ℂ
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
      =
    ∫ z : UC,
      (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand D.X D.H).indicator
        (fun x =>
          (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus D.X D.H x : ℝ) : ℂ) *
              star (D.ψ i x) * (D.ψ j x)) *
            (I.signalTorusByProd P W x) *
              star (I.signalTorusByProd P W x))
        z := by
  simpa using
    inner_eq_arcIntegral_rankOne (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (hsmall := hsmall) i j

end

end FejerBankedTypeIIToeplitzTTStarArcProof
end Instances
end SSU
