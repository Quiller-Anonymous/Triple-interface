import Goldbach.CompleteTenorFunX

/-!
Canonical “parallel FunX” budget hypotheses.

This file is meant to be a *paper-facing* checklist for the remaining analytic inputs needed to run
the FunX (variable-`Q`) parallel track end-to-end.

After switching to the honest, `N`-dependent σ-model (Option A), the older hard-coded constant
`sigma0 = 0.05` bookkeeping is no longer correct. We therefore keep this file purely as an
assumption bundle:
- a σ-upper bound (`AO_SigmaPos.SigmaUpperOnWindow`),
- a σ-lower bound (`AO_SigmaPos.SigmaLowerOnWindow`),
- the major-arc “inner swap” hypothesis on the canonical window,
- the global budget inequality feeding the closure bridge.

Nothing here asserts numeric values; those belong in dedicated certificate modules.
-/

namespace Goldbach

open Goldbach.Windows

namespace ParallelFunXCanon

/-- The canonical FunX off-diagonal package (already wired in `TenorHypFunX_Canon`). -/
noncomputable abbrev Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp :=
  Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff

/--
The canonical closure constant for this instantiation (`σmin − δAO`).

This depends on a σ-lower certificate on the canonical window, packaged as
`AO_SigmaPos.SigmaLowerOnWindow`.
-/
noncomputable abbrev c0 [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] : ℝ :=
  Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)

/-- Remaining hypotheses for the canonical FunX parallel track. -/
class BudgetHyp [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] : Prop where
  /-- Major-arc swap bound on the window (feeds `δAO_gap_bound`). -/
  innerSwap : Goldbach.ParallelTenorFunX.InnerSwapOnWindow
  /-- `ε < c0` for the canonical instantiation. -/
  eps_lt_c0 : (0.01 : ℝ) < c0
  /-- Global window budget used by `CompleteTenorFunX`. -/
  budget :
    ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ EvenIn X (10_000 : ℕ) →
      Goldbach.BG_Calib.δbridge_canon
        + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
        + @Goldbach.ParallelTenorFunX.δAO_gap_bound innerSwap Hoff ≤ (0.01 : ℝ)

/-- Canonical FunX track, with the remaining analytic hypotheses packaged as a single assumption. -/
theorem goldbach_from_tenorFunX_fun_auto
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    [BudgetHyp]
    (hBase : FiniteBaseUpTo 1_000_000) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  classical
  haveI : Goldbach.ParallelTenorFunX.InnerSwapOnWindow := BudgetHyp.innerSwap
  have hεlt : (0.01 : ℝ) < Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) := by
    simpa [c0] using (BudgetHyp.eps_lt_c0 : (0.01 : ℝ) < c0)
  have hBudget :
      ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ EvenIn X (10_000 : ℕ) →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) ≤ (0.01 : ℝ) := by
    intro X N hX hN
    simpa using (BudgetHyp.budget (X := X) (N := N) hX hN)
  exact Goldbach.goldbach_from_tenorFunX_fun_autoHoff
    (hεlt := hεlt)
    (hBudget := by
      intro X N hX hN
      exact hBudget hX hN)
    (hBase := hBase)

end ParallelFunXCanon

end Goldbach

