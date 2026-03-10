-- Goldbach/GoldFunX.lean
--
-- An end-to-end Goldbach theorem for the canonical (Tenor-aligned) parallel FunX track.
-- This is the “no user-supplied witness” entry point: the analytic witness is built
-- internally from the Tenor FunX pipeline and the remaining analytic assumptions are
-- isolated as explicit hypotheses (typeclasses), with optional pinned/certificate instances
-- living in the relevant `Cert/*` modules.

import Goldbach.CompleteTenorFunX_CanonBudget_Scale
import Goldbach.Cert.InnerSwapTextbookRoute
import Goldbach.FiniteBase.CombineAll
import Goldbach.BG_CalibBridgeStub
import Goldbach.CanonParams

namespace Goldbach

/-- Canonical end-to-end Goldbach theorem (parallel FunX track, `X0 = 1_000_000`). -/
theorem goldbach_funX_canon
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    [Goldbach.ParallelFunXCanonScale.BudgetHyp] :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  have hBase : FiniteBaseUpTo 1_000_000 := Goldbach.FiniteBase.finiteBaseUpTo_1e6
  exact Goldbach.ParallelFunXCanonScale.goldbach_from_tenorFunX_scale_auto (hBase := hBase)

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
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.CanonParams.ε <
          Goldbach.ParallelFunXCanonScale.c0 X)
    (hBudget :
      ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ Goldbach.Windows.EvenIn X (10_000 : ℕ) →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + @Goldbach.ParallelTenorFunX.δAO_gap_bound
              (Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_canonCalibration h)
              Goldbach.ParallelFunXCanonScale.Hoff X ≤ Goldbach.CanonParams.ε) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  haveI : Goldbach.ParallelFunXCanonScale.BudgetHyp :=
    { innerSwap := Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_canonCalibration h
    , eps_lt_c0_on_window := hεlt
    , budget := by
        intro X N hX hN
        simpa [Goldbach.CanonParams.ε] using hBudget hX hN }
  exact goldbach_funX_canon

end Goldbach
