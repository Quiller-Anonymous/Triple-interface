import SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof

/-!
Fejér-banked packets: **arc integral = Toeplitz form** (rank-one Type–II input).

This is the TeX “Toeplitz Type–II reduction” in its most literal form:

* start from the small-arc torus integral (after the deterministic band→arc substitution), and
* identify it with the grouped-by-product Toeplitz quadratic form `toeplitzFormTeXC`.

Technically this is just transitivity between the two already-proved statements in
`SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcProof.lean`, but it is convenient as a single
named lemma for downstream use.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzArcToeplitzRankOne

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus
open SSU.Engines.TypeII
open SSU.Engines.TypeIIToeplitz

variable {κ : Type*} [DecidableEq κ]

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : SSU.Engines.BGTypeIIRankOne.Input)

open SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal

private noncomputable def arcIntegrand (i j : ℤ) (x : UC) : ℂ :=
  (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus D.X D.H x : ℝ) : ℂ) *
        star (D.ψ i x) * (D.ψ j x)) *
    (I.signalTorusByProd P W x) * star (I.signalTorusByProd P W x)

private noncomputable def arcIntegral (i j : ℤ) : ℂ :=
  ∫ z : UC,
    (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand D.X D.H).indicator
      (arcIntegrand (D := D) (P := P) (W := W) (I := I) i j)
      z

theorem arcIntegral_eq_toeplitzFormTeXC_rankOne
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i j : ℤ) :
    arcIntegral (D := D) (P := P) (W := W) (I := I) i j
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := P.box)
        (F := fun p => I.F (P := P) (W := W) p) := by
  -- Both sides are equal to the same TT* Gram entry.
  have h1 :
      inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      ((1 / D.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
          (T := P.box)
          (F := fun p => I.F (P := P) (W := W) p) := by
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof.inner_eq_toeplitzFormTeXC_rankOne
        (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (i := i) (j := j))
  have h2 :
      inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      arcIntegral (D := D) (P := P) (W := W) (I := I) i j := by
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof.inner_eq_arcIntegral_rankOne
        (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (hsmall := hsmall) (i := i) (j := j))
  -- Conclude by transitivity.
  calc
    arcIntegral (D := D) (P := P) (W := W) (I := I) i j
        =
      inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H)) := by
              simpa using h2.symm
    _ =
      ((1 / D.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
          (T := P.box)
          (F := fun p => I.F (P := P) (W := W) p) := h1

end

end FejerBankedTypeIIToeplitzArcToeplitzRankOne
end Instances
end SSU
