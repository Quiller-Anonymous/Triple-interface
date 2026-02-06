import SSU.Instances.FejerBankedTypeIIToeplitzStep34Proof
import SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof

/-!
Fejér-banked packets: proved **Step 3–4 ⇒ arc-form TT*** Gram bound (rank-one Type–II input).

This is a thin wrapper combining:

* the proved Step 3–4 (`Step34ProdSum`) ⇒ TT* Gram bound on the ξ-band model packets, and
* the deterministic band→arc identity for those packets.

It produces the TeX-shaped statement “Gram entry = small-arc torus integral” together with the
Step 3–4 large sieve bound.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzStep34ArcProof

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

open SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar
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

theorem norm_arcIntegral_rankOne_le
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (step34 : Step34ProdSum D.X D.H P.box)
    (i j : ℤ) :
    ‖arcIntegral (D := D) (P := P) (W := W) (I := I) i j‖
      ≤
    ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
        (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))) *
      (2 * (D.H)⁻¹) := by
  -- Convert the arc integral back to the ξ-band TT* Gram entry, then apply the Step 3–4 bound.
  have hArc :
      inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        = arcIntegral (D := D) (P := P) (W := W) (I := I) i j := by
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof.inner_eq_arcIntegral_rankOne
        (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (hsmall := hsmall) (i := i) (j := j))
  have hNormInner :
      ‖inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))‖
        =
      ‖arcIntegral (D := D) (P := P) (W := W) (I := I) i j‖ := by
    simpa using congrArg (fun z : ℂ => ‖z‖) hArc
  have hBound :
      ‖inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))‖
        ≤
      ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
          (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))) *
        (2 * (D.H)⁻¹) :=
    (SSU.Instances.FejerBankedTypeIIToeplitzStep34Proof.norm_inner_packetOp_rankOne_le
      (D := D) (P := P) (W := W) (I := I) (hU := hU) (hX := hX) (hH := hH) (step34 := step34) (i := i) (j := j))
  -- Rewrite the bound to the arc integral form.
  -- (We keep the norm rewrite explicit; `simp` does not automatically use `hNormInner` in both directions.)
  calc
    ‖arcIntegral (D := D) (P := P) (W := W) (I := I) i j‖
        = ‖inner ℂ
            (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
              (D := D) (X := D.X) (H := D.H) hH hX i
              (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
            (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
              (D := D) (X := D.X) (H := D.H) hH hX j
              (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))‖ := by
              simpa using hNormInner.symm
    _ ≤
      ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
          (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))) *
        (2 * (D.H)⁻¹) := hBound

end

end FejerBankedTypeIIToeplitzStep34ArcProof
end Instances
end SSU
