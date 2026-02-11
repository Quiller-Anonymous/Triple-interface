import SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne
import SSU.Instances.FejerBankedTypeIIToeplitzStep34ToeplitzBound

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
  have hEq :=
    (RankOne.inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne
      (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (hsmall := hsmall) i j)
  -- Reduce to the existing Toeplitz bound.
  have hToep :=
    (SSU.Instances.FejerBankedTypeIIToeplitzStep34ToeplitzBound.norm_toeplitzFormTeXC_rankOne_le
      (D := D) (P := P) (W := W) (I := I) (hU := hU) (hX := hX) (hH := hH)
      (step34 := step34) (i := i) (j := j))
  -- `hToep` is exactly the bound for the RHS of `hEq`.
  simpa [hEq] using hToep

end

end FejerBankedTypeIIToeplitzTorusPacketsRankOneBound
end Instances
end SSU
