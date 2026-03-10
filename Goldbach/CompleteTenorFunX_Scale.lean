import Goldbach.CoreTypes
import Goldbach.AnalyticPointwiseScale
import Goldbach.AnalyticGlobalScale
import Goldbach.FinalScale
import Goldbach.ParallelTenorFunXCore
import Goldbach.AO_SigmaPos
import Goldbach.AO_OffDiag.TenorHypFunX_Canon
import Goldbach.BG_CalibBridgeStub
import Goldbach.CanonParams

open Goldbach
open Goldbach.Windows

namespace Goldbach.ParallelTenorFunXScale

/-- Scale-sensitive closure constant carried by the current AO/FunX route. -/
noncomputable abbrev c0
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] : ℕ → ℝ :=
  Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)

/-- Scale-sensitive projected main term carried by the current AO/FunX route. -/
noncomputable abbrev M
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) : ℕ → ℕ → ℝ :=
  Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff

/--
Scale-sensitive analytic hypothesis produced by the current AO/FunX route.

This is the honest replacement for the stale scalar-`c0` witness layer: `c0 X` is allowed to vary
with the scale, and the projected main term is `M X N = Mcanon Hoff X N`.
-/
def analyticHypScale_funX
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε < c0 Hoff X)
    (hBudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε) :
    Goldbach.AnalyticHypScale Goldbach.ParallelTenorFunX.X0
      (fun _ => Goldbach.ParallelTenorFunX.H)
      Goldbach.ParallelTenorFunX.S
      (c0 Hoff)
      Goldbach.ParallelTenorFunX.ε := by
  refine Goldbach.AnalyticHypScale.ofTenor ?_
  refine Goldbach.TenorHypScale.mkPack
    Goldbach.ParallelTenorFunX.X0
    (fun _ => Goldbach.ParallelTenorFunX.H)
    Goldbach.ParallelTenorFunX.S
    (c0 Hoff)
    Goldbach.ParallelTenorFunX.ε
    ?_ ?_ ?_ (M Hoff) ?_ ?_
  · norm_num [Goldbach.ParallelTenorFunX.S, Goldbach.CanonParams.S]
  ·
    intro X hX
    have hεnn : 0 ≤ Goldbach.ParallelTenorFunX.ε := by
      norm_num [Goldbach.ParallelTenorFunX.ε, Goldbach.CanonParams.ε]
    exact lt_of_le_of_lt hεnn (hεlt hX)
  ·
    intro X hX
    exact hεlt hX
  ·
    intro X N hX hN
    have hmajor :=
      Goldbach.AO_InstantiateTenorFunX.McanoN_lb_cAO
        (Hoff := Hoff) (X := X) (N := N) hX hN
    simpa [M, c0, Goldbach.ParallelTenorFunX.S, Goldbach.CanonParams.S] using hmajor
  ·
    intro X N hX hN
    have habs :=
      Goldbach.ParallelTenorFunX.bank_cert_bound_funX
        (Hoff := Hoff) (hBudget := hBudget) (X := X) (N := N) hX hN
    have hleft :
        -Goldbach.ParallelTenorFunX.ε ≤
          Goldbach.BG_Identity.R_bank X N - Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N :=
      (abs_le.mp habs).1
    have hbank :
        Goldbach.AO_InstantiateTenorFunX.Mcanon Hoff X N - Goldbach.ParallelTenorFunX.ε ≤
          Goldbach.BG_Identity.R_bank X N := by
      linarith
    simpa [M, Goldbach.ParallelTenorFunX.S, Goldbach.CanonParams.S] using hbank

/-- Package the scale-sensitive analytic hypothesis as a scale-sensitive pointwise witness. -/
noncomputable def witness_funX_scale
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε < c0 Hoff X)
    (hBudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε) :
    Goldbach.Analytic.PointwiseWitnessScale :=
  Goldbach.Analytic.PointwiseWitnessScale.ofAnalytic
    (analyticHypScale_funX (Hoff := Hoff) (hεlt := hεlt) (hBudget := hBudget))

end Goldbach.ParallelTenorFunXScale

namespace Goldbach

/--
Conditional final theorem at the canonical cutoff `X0 = 1_000_000`, using the scale-sensitive
normalization-aware FunX witness route.
-/
theorem goldbach_from_tenorFunX_scale
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε < Goldbach.ParallelTenorFunXScale.c0 Hoff X)
    (hBudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  let w : Goldbach.Analytic.PointwiseWitnessScale :=
    Goldbach.ParallelTenorFunXScale.witness_funX_scale
      (Hoff := Hoff) (hεlt := hεlt) (hBudget := hBudget)
  intro n hn h4
  exact Goldbach.goldbach_final_scale (w := w) (hBase := hBase) (N := n) hn h4

/--
Auto-`Hoff` wrapper for the scale-sensitive FunX route.

This keeps the next budget-layer refactor small by fixing the canonical off-diagonal package while
leaving the honest on-window positivity and budget hypotheses explicit.
-/
theorem goldbach_from_tenorFunX_scale_autoHoff
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.ParallelTenorFunX.ε
          < Goldbach.ParallelTenorFunXScale.c0
              Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff X)
    (hBudget :
      ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        N ∈ Goldbach.Windows.EvenIn X Goldbach.ParallelTenorFunX.H →
          Goldbach.BG_Calib.δbridge_canon
            + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
            + Goldbach.ParallelTenorFunX.δAO_gap_bound
                (Hoff := Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff) X
              ≤ Goldbach.ParallelTenorFunX.ε)
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  exact goldbach_from_tenorFunX_scale
    (Hoff := Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff)
    (hεlt := hεlt)
    (hBudget := hBudget)
    (hBase := hBase)

end Goldbach
