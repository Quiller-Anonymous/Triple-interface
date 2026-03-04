import SSU.Instances.FejerBankedTypeIIToeplitzRankOneStep34

/-!
Fejér-banked packets: proved **Step 3–4 ⇒ TT*** Gram bound (rank-one Type–II input).

This file is intentionally a thin wrapper around
`SSU/Instances/FejerBankedTypeIIToeplitzRankOneStep34.lean`.

It exists so downstream SSU-heart code can import a TeX-narrative filename (“Step 3–4 proof”)
without depending on implementation details (internal namespaces, helper lemmas, etc.).
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzStep34Proof

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

/--
Re-export: fixed-signal Step 3–4 (`Step34ProdSumFor`) implies a uniform TT* packet Gram bound for
the Fejér-banked real-frequency model packets, evaluated on the TeX rank-one Type–II signal.
-/
theorem norm_inner_packetOp_rankOne_le_of_step34For
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H)
    (step34 : Step34ProdSumFor D.X D.H P.box (fun p => I.F P W p))
    (i j : ℤ) :
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
      (2 * (D.H)⁻¹) := by
  simpa using
    (SSU.Instances.FejerBankedTypeIIToeplitzRankOneStep34.Gram.norm_inner_packetOp_rankOne_le_of_step34For
      (D := D) (P := P) (W := W) (I := I) (hU := hU) (hX := hX) (hH := hH)
      (step34 := step34) (i := i) (j := j))

/--
Re-export: Step 3–4 (`Step34ProdSum`) implies a uniform TT* packet Gram bound for the Fejér-banked
real-frequency model packets, evaluated on the TeX rank-one Type–II signal.
-/
theorem norm_inner_packetOp_rankOne_le
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H)
    (step34 : Step34ProdSum D.X D.H P.box)
    (i j : ℤ) :
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
      (2 * (D.H)⁻¹) := by
  exact
    norm_inner_packetOp_rankOne_le_of_step34For
      (D := D) (P := P) (W := W) (I := I)
      (hU := hU) (hX := hX) (hH := hH)
      (step34 := Step34ProdSumFor.of_global D.X D.H P.box step34 (fun p => I.F P W p))
      (i := i) (j := j)

end

end FejerBankedTypeIIToeplitzStep34Proof
end Instances
end SSU
