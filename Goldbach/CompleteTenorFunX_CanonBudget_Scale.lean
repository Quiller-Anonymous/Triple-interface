import Goldbach.CompleteTenorFunX_Scale
import Goldbach.CanonParams

/-!
Canonical budget hypotheses for the scale-sensitive FunX route.

This is the normalization-aware analogue of `CompleteTenorFunX_CanonBudget`.  The only structural
change is that the AO closure margin is now treated honestly as `c0 X`, so positivity is assumed
on-window as `ε < c0 X` for every `X ≥ X0`.
-/

namespace Goldbach

open Goldbach.Windows

namespace ParallelFunXCanonScale

/-- The canonical FunX off-diagonal package. -/
noncomputable abbrev Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp :=
  Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff

/-- The canonical scale-sensitive closure margin for the FunX route. -/
noncomputable abbrev c0 [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] : ℕ → ℝ :=
  Goldbach.ParallelTenorFunXScale.c0 Hoff

/-- Remaining hypotheses for the canonical scale-sensitive FunX route. -/
class BudgetHyp [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] where
  /-- Major-arc swap bound on the canonical window. -/
  innerSwap : Goldbach.ParallelTenorFunX.InnerSwapOnWindow
  /-- Honest on-window positivity margin for the scale-sensitive closure constant. -/
  eps_lt_c0_on_window :
    ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X → Goldbach.CanonParams.ε < c0 X
  /-- Global window budget feeding the bank certificate. -/
  budget :
    ∀ {X N : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
      N ∈ EvenIn X Goldbach.ParallelTenorFunX.H →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + @Goldbach.ParallelTenorFunX.δAO_gap_bound innerSwap Hoff X
            ≤ Goldbach.CanonParams.ε

/-- Canonical scale-sensitive FunX route, with the remaining analytic inputs bundled together. -/
theorem goldbach_from_tenorFunX_scale_auto
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    [BudgetHyp]
    (hBase : FiniteBaseUpTo Goldbach.ParallelTenorFunX.X0) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  classical
  letI : Goldbach.ParallelTenorFunX.InnerSwapOnWindow := BudgetHyp.innerSwap
  exact Goldbach.goldbach_from_tenorFunX_scale_autoHoff
    (hεlt := BudgetHyp.eps_lt_c0_on_window)
    (hBudget := by
      intro X N hX hN
      simpa [Goldbach.CanonParams.ε] using (BudgetHyp.budget (X := X) (N := N) hX hN))
    (hBase := hBase)

end ParallelFunXCanonScale

end Goldbach
