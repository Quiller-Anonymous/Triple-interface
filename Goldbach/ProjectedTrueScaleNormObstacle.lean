import Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare

namespace Goldbach.ProjectedTrueScaleNormObstacle

open Goldbach
open Goldbach.Windows

noncomputable section

/--
At the canonical basepoint, the naive `scaleNorm` major clause with

* analytic model `M(X,N) = RΛ_model(X,N)`,
* closure margin `c0(X) = Ltrue(X)`,
* scale `S(X) = Strue_from_RΛ_model(X)`

has the wrong polarity: it would require the normalized model to dominate a quantity strictly
larger than `Ltrue(X0)`, while the model is already strictly below `Ltrue(X0)`.
-/
theorem not_naive_scaleNorm_major_at_X0 :
    ¬ (Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0
          * Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.Strue_from_RΛ_model Goldbach.Analytic.X0
        ≤ Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model Goldbach.Analytic.X0 Goldbach.Analytic.X0) := by
  have hRlt :
      Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model Goldbach.Analytic.X0 Goldbach.Analytic.X0
        < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 :=
    Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.RΛ_model_at_X0_lt_Ltrue_at_X0
  have hSgt :
      (1 : ℝ)
        < Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.Strue_from_RΛ_model Goldbach.Analytic.X0 :=
    Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.one_lt_Strue_from_RΛ_model_at_X0
  have hLgt :
      (0 : ℝ) < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
    exact lt_trans (by norm_num) Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.one_lt_Ltrue_at_X0
  have hLmul :
      Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0
        < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0
            * Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.Strue_from_RΛ_model Goldbach.Analytic.X0 := by
    nlinarith
  have hRlt_mul :
      Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model Goldbach.Analytic.X0 Goldbach.Analytic.X0
        <
      Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0
        * Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.Strue_from_RΛ_model Goldbach.Analytic.X0 := by
    exact lt_trans hRlt hLmul
  exact not_le_of_gt hRlt_mul

/--
So the naive window-uniform major clause for the existing `scaleNorm` wrapper is false.
-/
theorem not_naive_scaleNorm_major_on_window :
    ¬ (∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
          N ∈ EvenIn X Goldbach.Analytic.H →
            Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X
              * Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare.Strue_from_RΛ_model X
            ≤ Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N) := by
  intro h
  have hmem : Goldbach.Analytic.X0 ∈ EvenIn Goldbach.Analytic.X0 Goldbach.Analytic.H := by
    exact Goldbach.Windows.mem_EvenIn_self
      (Goldbach.Windows.isEven_of_even (by decide : Even Goldbach.Analytic.X0))
  exact not_naive_scaleNorm_major_at_X0 (h le_rfl hmem)

end

end Goldbach.ProjectedTrueScaleNormObstacle
