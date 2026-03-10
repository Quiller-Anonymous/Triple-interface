import Goldbach.CoreTypes
import Goldbach.AnalyticPointwiseScaleNormEps
import Goldbach.AnalyticGlobalScaleNormEps
import Goldbach.FinalScaleNormEps
import Goldbach.ParallelTenorFunXCore
import Goldbach.AO_SigmaPos
import Goldbach.AO_OffDiag.TenorHypFunX_Canon
import Goldbach.BG_CalibBridgeStub
import Goldbach.CanonParams

open Goldbach
open Goldbach.Windows

namespace Goldbach.ParallelTenorFunXScaleNormEps

/-- AO closure margin from the current FunX route, reused in the variable-slack wrapper. -/
noncomputable abbrev c0
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] : ℕ → ℝ :=
  Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)

/-- Staged major term from the current FunX route, reused in the variable-slack wrapper. -/
noncomputable abbrev M
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) : ℕ → ℕ → ℝ :=
  Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff

/--
Variable-scale, variable-slack analytic hypothesis produced from the current AO/FunX route once
the user supplies normalization data `S(X)` and a local slack profile `ε(X)`.
-/
def analyticHypScaleNormEps_funX
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (S c0 eps : ℕ → ℝ)
    (hS_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < S X)
    (hc0_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < c0 X)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → eps X < c0 X)
    (hmajor :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        c0 X * S X ≤ Goldbach.ParallelTenorFunXScaleNormEps.c0 Hoff X)
    (hbudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hbank_scale :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε ≤ eps X * S X) :
    Goldbach.AnalyticHypScaleNormEps Goldbach.ParallelTenorFunX.X0
      (fun _ => Goldbach.ParallelTenorFunX.H)
      S
      c0
      eps := by
  refine Goldbach.AnalyticHypScaleNormEps.ofTenor ?_
  refine Goldbach.TenorHypScaleNormEps.mkPack
    Goldbach.ParallelTenorFunX.X0
    (fun _ => Goldbach.ParallelTenorFunX.H)
    S
    c0
    eps
    ?_ ?_ ?_
    (Goldbach.ParallelTenorFunXScaleNormEps.M Hoff)
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
        Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N - eps X * S X ≤
          Goldbach.BG_Identity.R_bank X N := by
      have hscale := hbank_scale hX
      linarith
    simpa [Goldbach.ParallelTenorFunXScaleNormEps.M] using hbank1

/--
Convenient specialization where the local slack is chosen to be exactly the raw bank slack divided
by the chosen normalization scale.
-/
def analyticHypScaleNormEps_funX_div
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (S c0 : ℕ → ℝ)
    (hS_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < S X)
    (hc0_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < c0 X)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε / S X < c0 X)
    (hmajor :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        c0 X * S X ≤ Goldbach.ParallelTenorFunXScaleNormEps.c0 Hoff X)
    (hbudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε) :
    Goldbach.AnalyticHypScaleNormEps Goldbach.ParallelTenorFunX.X0
      (fun _ => Goldbach.ParallelTenorFunX.H)
      S
      c0
      (fun X => Goldbach.ParallelTenorFunX.ε / S X) := by
  refine analyticHypScaleNormEps_funX
    (Hoff := Hoff) (S := S) (c0 := c0) (eps := fun X => Goldbach.ParallelTenorFunX.ε / S X)
    (hS_pos := hS_pos) (hc0_pos := hc0_pos) (hεlt := hεlt) (hmajor := hmajor)
    (hbudget := hbudget) ?_
  intro X hX
  have hSne : S X ≠ 0 := ne_of_gt (hS_pos hX)
  have : (Goldbach.ParallelTenorFunX.ε / S X) * S X = Goldbach.ParallelTenorFunX.ε := by
    field_simp [hSne]
  simpa using le_of_eq this.symm

/-- Package the variable-scale, variable-slack analytic hypothesis as a witness. -/
noncomputable def witness_funX_scaleNormEps
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (S c0 eps : ℕ → ℝ)
    (hS_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < S X)
    (hc0_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < c0 X)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → eps X < c0 X)
    (hmajor :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        c0 X * S X ≤ Goldbach.ParallelTenorFunXScaleNormEps.c0 Hoff X)
    (hbudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hbank_scale :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε ≤ eps X * S X) :
    Goldbach.Analytic.PointwiseWitnessScaleNormEps :=
  Goldbach.Analytic.PointwiseWitnessScaleNormEps.ofAnalytic
    (analyticHypScaleNormEps_funX
      (Hoff := Hoff) (S := S) (c0 := c0) (eps := eps)
      (hS_pos := hS_pos) (hc0_pos := hc0_pos) (hεlt := hεlt)
      (hmajor := hmajor) (hbudget := hbudget) (hbank_scale := hbank_scale))

end Goldbach.ParallelTenorFunXScaleNormEps

namespace Goldbach

/-- Conditional final theorem for the variable-scale, variable-slack normalization route. -/
theorem goldbach_from_tenorFunX_scaleNormEps
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (S c0 eps : ℕ → ℝ)
    (hS_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < S X)
    (hc0_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < c0 X)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → eps X < c0 X)
    (hmajor :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        c0 X * S X ≤ Goldbach.ParallelTenorFunXScaleNormEps.c0 Hoff X)
    (hbudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hbank_scale :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε ≤ eps X * S X)
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  let w : Goldbach.Analytic.PointwiseWitnessScaleNormEps :=
    Goldbach.ParallelTenorFunXScaleNormEps.witness_funX_scaleNormEps
      (Hoff := Hoff) (S := S) (c0 := c0) (eps := eps)
      (hS_pos := hS_pos) (hc0_pos := hc0_pos) (hεlt := hεlt)
      (hmajor := hmajor) (hbudget := hbudget) (hbank_scale := hbank_scale)
  intro n hn h4
  exact Goldbach.goldbach_final_scaleNormEps (w := w) (hBase := hBase) (N := n) hn h4

/--
Auto-`ε(X) = ε_raw / S(X)` wrapper for the third normalization route.

This isolates the remaining analytic requirement to the local comparison
`ε_raw / S(X) < c0(X)`, equivalently `ε_raw < c0(X) * S(X)`.
-/
theorem goldbach_from_tenorFunX_scaleNormEps_div
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (S c0 : ℕ → ℝ)
    (hS_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < S X)
    (hc0_pos :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → 0 < c0 X)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε / S X < c0 X)
    (hmajor :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        c0 X * S X ≤ Goldbach.ParallelTenorFunXScaleNormEps.c0 Hoff X)
    (hbudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  let eps : ℕ → ℝ := fun X => Goldbach.ParallelTenorFunX.ε / S X
  exact goldbach_from_tenorFunX_scaleNormEps
    (Hoff := Hoff) (S := S) (c0 := c0) (eps := eps)
    (hS_pos := hS_pos) (hc0_pos := hc0_pos) (hεlt := hεlt)
    (hmajor := hmajor) (hbudget := hbudget)
    (hbank_scale := by
      intro X hX
      have hSne : S X ≠ 0 := ne_of_gt (hS_pos hX)
      have : (Goldbach.ParallelTenorFunX.ε / S X) * S X = Goldbach.ParallelTenorFunX.ε := by
        field_simp [hSne]
      simpa [eps] using le_of_eq this.symm)
    (hBase := hBase)

end Goldbach
