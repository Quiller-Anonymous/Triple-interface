import Goldbach.ProjectedMajorTermDirectProto
import Goldbach.FinalDirect
import Goldbach.BG_CalibBridgeStub
import Goldbach.BankPieces.Cert.ProjectedInput

namespace Goldbach.ProjectedMajorTermDirectCanon

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic

noncomputable section

/-- Canonical projected additive gap candidate from the refactored bank-gap route. -/
noncomputable abbrev Δproj (X : ℕ) : ℝ :=
  Goldbach.BankPieces.Cert.ProjectedInput.Δproj X

/-- The canonical projected pointwise witness, if the projected gap is eventually below `Lproj`. -/
noncomputable def pointwiseWitness
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hgap_lt_lower :
      ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X →
        Δproj X < Goldbach.ProjectedMajorTermDirectProto.Lproj X) :
    Goldbach.Analytic.PointwiseWitnessDirect :=
  Goldbach.ProjectedMajorTermDirectProto.pointwiseWitness_projected
    (Δ := Δproj)
    (gap_nonneg := by
      intro X hX
      simpa using (Goldbach.BankPieces.Cert.ProjectedInput.Δproj_nonneg (X := X)))
    (gap_lt_lower := by
      intro X hX
      exact hgap_lt_lower hX)
    (bank_gap := by
      intro X N hX hN
      exact Goldbach.ProjectedMajorTermDirectProto.bank_gap_from_actual_projected_input
        (X := X) (N := N) hX hN)

/-- Final Goldbach theorem on the projected direct route, once the projected gap closes. -/
theorem goldbach_final_projected
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBase : Goldbach.Base.FiniteBaseUpTo Goldbach.Analytic.X0)
    (hgap_lt_lower :
      ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X →
        Δproj X < Goldbach.ProjectedMajorTermDirectProto.Lproj X) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.Base.GoldbachRep N := by
  exact Goldbach.goldbach_final_direct
    (w := pointwiseWitness hgap_lt_lower)
    hBase

/--
On even points of the canonical window, the current projected gap dominates `Lproj`.

So the projected direct route is now a real theorem surface, but it still does not close with the
current coarse projected input `Δproj`.
-/
theorem Lproj_le_Δproj_of_even
    {X : ℕ} [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hX : Goldbach.Analytic.X0 ≤ X) (hEven : Goldbach.Windows.IsEven X) :
    Goldbach.ProjectedMajorTermDirectProto.Lproj X ≤ Δproj X := by
  have hmem : X ∈ EvenIn X Goldbach.Analytic.H :=
    Goldbach.Windows.mem_EvenIn_self hEven
  have hlower :
      Goldbach.ProjectedMajorTermDirectProto.Lproj X
        ≤ Goldbach.ProjectedMajorTermDirectProto.Mproj X X :=
    Goldbach.ProjectedMajorTermDirectProto.projected_major_lower hX hmem
  have hmain :
      Goldbach.ProjectedMajorTermDirectProto.Mproj X X
        ≤ Goldbach.BankPieces.Cert.ProjectedInput.Δref_proj X := by
    simpa [Goldbach.ProjectedMajorTermDirectProto.Mproj] using
      (Goldbach.BankPieces.Cert.ProjectedInput.mainTerm_le_Δref_proj
        (X := X) (N := X) hX hmem)
  have href :
      Goldbach.BankPieces.Cert.ProjectedInput.Δref_proj X ≤ Δproj X :=
    Goldbach.BankPieces.Cert.ProjectedInput.Δref_proj_le_Δproj (X := X)
  exact le_trans hlower (le_trans hmain href)

/-- The current projected gap does not beat the projected lower term at even canonical scales. -/
theorem not_Δproj_lt_Lproj_of_even
    {X : ℕ} [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hX : Goldbach.Analytic.X0 ≤ X) (hEven : Goldbach.Windows.IsEven X) :
    ¬ Δproj X < Goldbach.ProjectedMajorTermDirectProto.Lproj X := by
  exact not_lt_of_ge (Lproj_le_Δproj_of_even hX hEven)

/--
Concrete canonical obstruction: the projected direct route already fails at the basepoint `X0`.

This isolates the remaining work cleanly: the next normalization improvement has to shrink `Δproj`,
not just repackage the direct closure route.
-/
theorem not_Δproj_lt_Lproj_at_X0
    [Goldbach.BG_Calib.WeightsBridgeHyp] :
    ¬ Δproj Goldbach.Analytic.X0
        < Goldbach.ProjectedMajorTermDirectProto.Lproj Goldbach.Analytic.X0 := by
  have hX : Goldbach.Analytic.X0 ≤ Goldbach.Analytic.X0 := le_rfl
  have hEven : Goldbach.Windows.IsEven Goldbach.Analytic.X0 := by
    exact Goldbach.Windows.isEven_of_even (by decide : Even Goldbach.Analytic.X0)
  exact not_Δproj_lt_Lproj_of_even hX hEven

end

end Goldbach.ProjectedMajorTermDirectCanon
