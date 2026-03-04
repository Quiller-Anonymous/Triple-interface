import SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne
import SSU.Instances.FejerBankedTypeIIToeplitzStep34ToeplitzBound
import SSU.Engines.BGTypeIIRankOneToyMV

/-!
Fejér-banked packets (torus-side): **rank-one Type–II input ⇒ Toeplitz bound**.

This is the first non-toy “extraction” wrapper we need downstream:

* `inner(packetOp i fTT, packetOp j fTT) = (1/X) * toeplitzFormTeXC` (proved in the torus packet model), and
* the already-proved Step 3–4 Toeplitz bound for rank-one Type–II signals.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzTorusPacketsRankOneBound

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus

open SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne

variable {κ : Type*} [DecidableEq κ]

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : SSU.Engines.BGTypeIIRankOne.Input)

theorem norm_inner_packetOpUnnormalized_rankOne_le_of_step34For
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (step34 : SSU.Engines.TypeIIToeplitz.Step34ProdSumFor D.X D.H P.box (fun p => I.F P W p))
    (i j : ℤ) :
    ‖inner ℂ
        (((D.toMultiplierModel).packetOpUnnormalized i)
          (RankOne.fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j)
          (RankOne.fTT (D := D) (P := P) (W := W) (I := I) hH))‖
      ≤
    ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
        (step34.C * Real.sqrt (D.H / D.X) *
          SSU.tubeEnergy P.box (fun p => I.F (P := P) (W := W) p))) *
      (2 * (D.H)⁻¹) := by
  have hEq :=
    (RankOne.inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne
      (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (hsmall := hsmall) i j)
  have hToep :=
    (SSU.Instances.FejerBankedTypeIIToeplitzStep34ToeplitzBound.norm_toeplitzFormTeXC_rankOne_le_of_step34For
      (D := D) (P := P) (W := W) (I := I) (hU := hU) (hX := hX) (hH := hH)
      (step34 := step34) (i := i) (j := j))
  simpa [hEq] using hToep

theorem norm_inner_packetOpUnnormalized_rankOne_le
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (step34 : SSU.Engines.TypeIIToeplitz.Step34ProdSum D.X D.H P.box)
    (i j : ℤ) :
    ‖inner ℂ
        (((D.toMultiplierModel).packetOpUnnormalized i)
          (RankOne.fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j)
          (RankOne.fTT (D := D) (P := P) (W := W) (I := I) hH))‖
      ≤
    ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
        (step34.C * Real.sqrt (D.H / D.X) *
          SSU.tubeEnergy P.box (fun p => I.F (P := P) (W := W) p))) *
      (2 * (D.H)⁻¹) := by
  exact
    norm_inner_packetOpUnnormalized_rankOne_le_of_step34For
      (D := D) (P := P) (W := W) (I := I)
      (hU := hU) (hX := hX) (hH := hH) (hsmall := hsmall)
      (step34 := SSU.Engines.TypeIIToeplitz.Step34ProdSumFor.of_global D.X D.H P.box step34
        (fun p => I.F P W p))
      (i := i) (j := j)

theorem norm_inner_packetOpUnnormalized_rankOne_le_box_rankOne_uniform
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (hXeq : D.X = (P.X : ℝ)) (hHeq : D.H = (P.H : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hXH1 : 1 ≤ D.X * D.H)
    (hXH_box :
      (2 : ℝ) * ((Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1)) : ℕ) : ℝ) ≤ D.X * D.H)
    (i j : ℤ) :
    let step34 : SSU.Engines.TypeIIToeplitz.Step34ProdSumFor D.X D.H P.box (fun p => I.F P W p) :=
      by
        simpa [hXeq, hHeq] using
          (I.step34ProdSumFor_box_rankOne_uniform
            (P := P) (W := W) (hU := hU)
            (hD1 := hD1) (hU1 := hU1)
            (hX := by
              have hXR : 0 < (P.X : ℝ) := by simpa [hXeq] using hX
              exact_mod_cast hXR)
            (hH := by
              have hHR : 0 < (P.H : ℝ) := by simpa [hHeq] using hH
              exact_mod_cast hHR)
            (hXH1 := by simpa [hXeq, hHeq] using hXH1)
            (hXH_box := by simpa [hXeq, hHeq] using hXH_box))
    ‖inner ℂ
        (((D.toMultiplierModel).packetOpUnnormalized i)
          (RankOne.fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j)
          (RankOne.fTT (D := D) (P := P) (W := W) (I := I) hH))‖
      ≤
    ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
        (step34.C *
          Real.sqrt (D.H / D.X) * SSU.tubeEnergy P.box (fun p => I.F (P := P) (W := W) p))) *
      (2 * (D.H)⁻¹) := by
  let step34P :=
    I.step34ProdSumFor_box_rankOne_uniform
      (P := P) (W := W) (hU := hU)
      (hD1 := hD1) (hU1 := hU1)
      (hX := by
        have hXR : 0 < (P.X : ℝ) := by simpa [hXeq] using hX
        exact_mod_cast hXR)
      (hH := by
        have hHR : 0 < (P.H : ℝ) := by simpa [hHeq] using hH
        exact_mod_cast hHR)
      (hXH1 := by simpa [hXeq, hHeq] using hXH1)
      (hXH_box := by simpa [hXeq, hHeq] using hXH_box)
  let step34 : SSU.Engines.TypeIIToeplitz.Step34ProdSumFor D.X D.H P.box (fun p => I.F P W p) := by
    simpa [hXeq, hHeq] using step34P
  dsimp [step34]
  simpa [step34P] using
    norm_inner_packetOpUnnormalized_rankOne_le_of_step34For
      (D := D) (P := P) (W := W) (I := I)
      (hU := hU) (hX := hX) (hH := hH) (hsmall := hsmall)
      (step34 := (by
        simpa [step34P, hXeq, hHeq] using step34P :
          SSU.Engines.TypeIIToeplitz.Step34ProdSumFor D.X D.H P.box (fun p => I.F P W p)))
      (i := i) (j := j)

end

end FejerBankedTypeIIToeplitzTorusPacketsRankOneBound
end Instances
end SSU
