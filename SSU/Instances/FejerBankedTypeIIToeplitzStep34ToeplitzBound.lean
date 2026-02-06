import SSU.Instances.FejerBankedTypeIIToeplitzStep34Proof
import SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof

/-!
Fejér-banked packets: **Step 3–4 ⇒ Toeplitz-form bound** (rank-one Type–II input).

This is a TeX-friendly restatement:

* use the proved identity `inner = (1/X) * toeplitzFormTeXC`, and
* apply the proved Step 3–4 (`Step34ProdSum`) Gram bound.

The result is a direct estimate for the grouped-by-product Toeplitz quadratic form.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzStep34ToeplitzBound

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

theorem norm_toeplitzFormTeXC_rankOne_le
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H)
    (step34 : Step34ProdSum D.X D.H P.box)
    (i j : ℤ) :
    ‖((1 / D.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
          (T := P.box)
          (F := fun p => I.F (P := P) (W := W) p)‖
      ≤
    ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
        (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))) *
      (2 * (D.H)⁻¹) := by
  -- Rewrite the normalized Toeplitz form as the TT* Gram entry, then apply the Step 3–4 bound.
  have htoe :
      inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S
              (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S
              (D := D) (I := I) (P := P) (W := W) D.X D.H))
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
  have hStep34 :
      ‖inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S
              (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S
              (D := D) (I := I) (P := P) (W := W) D.X D.H))‖
        ≤
      ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
          (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))) *
        (2 * (D.H)⁻¹) :=
    (SSU.Instances.FejerBankedTypeIIToeplitzStep34Proof.norm_inner_packetOp_rankOne_le
      (D := D) (P := P) (W := W) (I := I) (hU := hU) (hX := hX) (hH := hH)
      (step34 := step34) (i := i) (j := j))
  have hnorm :
      ‖((1 / D.X : ℝ) : ℂ) *
            SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
              (K := fun t =>
                SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
              (T := P.box)
              (F := fun p => I.F (P := P) (W := W) p)‖
        =
      ‖inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S
              (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S
              (D := D) (I := I) (P := P) (W := W) D.X D.H))‖ := by
    simpa [htoe] using congrArg (fun z : ℂ => ‖z‖) htoe.symm
  -- Rewrite by `hnorm` and apply the Step 3–4 bound.
  -- (Use `rw` rather than `simp` to avoid expanding the LHS norm.)
  rw [hnorm]
  exact hStep34

end

end FejerBankedTypeIIToeplitzStep34ToeplitzBound
end Instances
end SSU
