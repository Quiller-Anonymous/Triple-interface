import Goldbach.CoreTypes
import Goldbach.AnalyticPointwiseScaleNorm
import Goldbach.AnalyticGlobalScaleNorm
import Goldbach.FinalScaleNorm
import Goldbach.ParallelTenorFunXCore
import Goldbach.AO_SigmaPos
import Goldbach.AO_OffDiag.TenorHypFunX_Canon
import Goldbach.BG_CalibBridgeStub
import Goldbach.CanonParams

open Goldbach
open Goldbach.Windows

namespace Goldbach.ParallelTenorFunXScaleNorm

/-- AO closure margin from the current FunX route, reused in the variable-scale wrapper. -/
noncomputable abbrev c0
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] : ℕ → ℝ :=
  Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)

/-- Staged major term from the current FunX route, reused in the variable-scale wrapper. -/
noncomputable abbrev M
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) : ℕ → ℕ → ℝ :=
  Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff

/--
Variable-scale analytic hypothesis produced from the current AO/FunX route once the user supplies
the new normalization data `S(X)` and the two compatibility inequalities it must satisfy.
-/
def analyticHypScaleNorm_funX
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (S c0 : ℕ → ℝ)
    (ε : ℝ)
    (hS_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < S X)
    (hc0_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X -> 0 < c0 X)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X -> ε < c0 X)
    (hmajor :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        c0 X * S X ≤ Goldbach.ParallelTenorFunXScaleNorm.c0 Hoff X)
    (hbudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hbank_scale :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X ->
        Goldbach.ParallelTenorFunX.ε ≤ ε * S X) :
    Goldbach.AnalyticHypScaleNorm Goldbach.ParallelTenorFunX.X0
      (fun _ => Goldbach.ParallelTenorFunX.H)
      S
      c0
      ε := by
  refine Goldbach.AnalyticHypScaleNorm.ofTenor ?_
  refine Goldbach.TenorHypScaleNorm.mkPack
    Goldbach.ParallelTenorFunX.X0
    (fun _ => Goldbach.ParallelTenorFunX.H)
    S
    c0
    ε
    ?_ ?_ ?_
    (Goldbach.ParallelTenorFunXScaleNorm.M Hoff)
    ?_ ?_
  · intro X hX; exact hS_pos hX
  · intro X hX; exact hc0_pos hX
  · intro X hX; exact hεlt hX
  ·
    intro X N hX hN
    have hmajor0 :=
      Goldbach.AO_InstantiateTenorFunX.McanoN_lb_cAO
        (Hoff := Hoff) (X := X) (N := N) hX hN
    exact le_trans (hmajor hX) hmajor0
  ·
    intro X N hX hN
    have habs :=
      Goldbach.ParallelTenorFunX.bank_cert_bound_funX
        (Hoff := Hoff) (hBudget := hbudget) (X := X) (N := N) hX hN
    have hleft :
        -Goldbach.ParallelTenorFunX.ε ≤
          Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N :=
      (abs_le.mp habs).1
    have hbank0 :
        Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N - Goldbach.ParallelTenorFunX.ε ≤
          Goldbach.BG_Identity.R_bank X N := by
      linarith
    have hbank1 :
        Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N - ε * S X ≤
          Goldbach.BG_Identity.R_bank X N := by
      have hscale := hbank_scale hX
      linarith
    simpa [Goldbach.ParallelTenorFunXScaleNorm.M] using hbank1

/-- Package the variable-scale analytic hypothesis as a witness. -/
noncomputable def witness_funX_scaleNorm
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (S c0 : ℕ → ℝ)
    (ε : ℝ)
    (hS_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X -> 0 < S X)
    (hc0_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X -> 0 < c0 X)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X -> ε < c0 X)
    (hmajor :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X ->
        c0 X * S X ≤ Goldbach.ParallelTenorFunXScaleNorm.c0 Hoff X)
    (hbudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X ->
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H ->
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hbank_scale :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X ->
        Goldbach.ParallelTenorFunX.ε ≤ ε * S X) :
    Goldbach.Analytic.PointwiseWitnessScaleNorm :=
  Goldbach.Analytic.PointwiseWitnessScaleNorm.ofAnalytic
    (analyticHypScaleNorm_funX
      (Hoff := Hoff) (S := S) (c0 := c0) (ε := ε)
      (hS_pos := hS_pos) (hc0_pos := hc0_pos) (hεlt := hεlt)
      (hmajor := hmajor) (hbudget := hbudget) (hbank_scale := hbank_scale))

end Goldbach.ParallelTenorFunXScaleNorm

namespace Goldbach

/--
Conditional final theorem for the variable-scale normalization route.
-/
theorem goldbach_from_tenorFunX_scaleNorm
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (S c0 : ℕ → ℝ)
    (ε : ℝ)
    (hS_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X -> 0 < S X)
    (hc0_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X -> 0 < c0 X)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X -> ε < c0 X)
    (hmajor :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X ->
        c0 X * S X ≤ Goldbach.ParallelTenorFunXScaleNorm.c0 Hoff X)
    (hbudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X ->
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H ->
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hbank_scale :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X ->
        Goldbach.ParallelTenorFunX.ε ≤ ε * S X)
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  let w : Goldbach.Analytic.PointwiseWitnessScaleNorm :=
    Goldbach.ParallelTenorFunXScaleNorm.witness_funX_scaleNorm
      (Hoff := Hoff) (S := S) (c0 := c0) (ε := ε)
      (hS_pos := hS_pos) (hc0_pos := hc0_pos) (hεlt := hεlt)
      (hmajor := hmajor) (hbudget := hbudget) (hbank_scale := hbank_scale)
  intro n hn h4
  exact Goldbach.goldbach_final_scaleNorm (w := w) (hBase := hBase) (N := n) hn h4

end Goldbach
