-- Goldbach/GoldFunX.lean
--
-- An end-to-end Goldbach theorem for the canonical (Tenor-aligned) parallel FunX track.
-- This is the “no user-supplied witness” entry point: the analytic witness is built
-- internally from the Tenor FunX pipeline and the remaining analytic assumptions are
-- isolated as explicit hypotheses (typeclasses), with optional pinned/certificate instances
-- living in the relevant `Cert/*` modules.

import Goldbach.CompleteTenorFunX_CanonBudget
import Goldbach.Cert.InnerSwapTextbookRoute
import Goldbach.FiniteBase.CombineAll
import Goldbach.BG_CalibBridgeStub

namespace Goldbach

/-- Canonical end-to-end Goldbach theorem (parallel FunX track, `X0 = 1_000_000`). -/
theorem goldbach_funX_canon
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    [Goldbach.ParallelFunXCanon.BudgetHyp] :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  have hBase : FiniteBaseUpTo 1_000_000 := Goldbach.FiniteBase.finiteBaseUpTo_1e6
  exact Goldbach.ParallelFunXCanon.goldbach_from_tenorFunX_fun_auto (hBase := hBase)

/--
Canonical end-to-end Goldbach theorem, assuming a major-arc calibration datum.

This is the “textbook route” entry point: `CanonicalCalibration` implies the required
`InnerSwapOnWindow` hypothesis via `Goldbach.Cert.InnerSwapTextbookRoute`.
-/
theorem goldbach_funX_canon_of_canonCalibration
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (h : Goldbach.Cert.MajorArcCalibrationFunX.CanonicalCalibration)
    (hεlt : (0.01 : ℝ) < Goldbach.ParallelFunXCanon.c0)
    (hBudget :
      ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ Goldbach.Windows.EvenIn X (10_000 : ℕ) →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + @Goldbach.ParallelTenorFunX.δAO_gap_bound
              (Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_canonCalibration h)
              Goldbach.ParallelFunXCanon.Hoff ≤ (0.01 : ℝ)) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  haveI : Goldbach.ParallelFunXCanon.BudgetHyp :=
    { innerSwap := Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_canonCalibration h
    , eps_lt_c0 := hεlt
    , budget := by
        intro X N hX hN
        exact hBudget hX hN }
  exact goldbach_funX_canon

end Goldbach
