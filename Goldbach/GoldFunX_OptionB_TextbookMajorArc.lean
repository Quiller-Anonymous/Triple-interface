import Goldbach.GoldFunX
import Goldbach.Cert.SigmaBoundsCanon
import Goldbach.Cert.InnerSwapOnWindowPowerSavingSpec
import Goldbach.CanonParams

/-!
Option B (textbook major-arc boundary).

This is the “gold-grade” (axiom-transparent) Option-B entry point:
- σ upper/lower bounds are supplied by canonical instances in `Goldbach.Cert.SigmaBoundsCanon`;
- the major-arc inner swap is supplied by the conventional `MajorArcPowerSaving` axiom boundary
  (wired via `Goldbach.Cert.InnerSwapOnWindowPowerSavingSpec`);
- the remaining global budget inequality is *still* an explicit hypothesis, as in `Goldbach.GoldFunX`.

This file intentionally does **not** attempt to discharge any pinned numeric calibration (those are
project-specific constants/certificates, not part of the conventional major-arc boundary).
-/

namespace Goldbach

open Goldbach.Windows

/-- Canonical FunX Goldbach theorem, using the textbook major-arc boundary and assuming the remaining
global budget inequality. -/
theorem goldbach_funX_canon_optionB_textbookMajorArc
    (hεlt : Goldbach.CanonParams.ε <
      Goldbach.AO_Major.cAO
        (Goldbach.AO_InstantiateTenorFunX.caps Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff))
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBudget :
      ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ EvenIn X (10_000 : ℕ) →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + Goldbach.ParallelTenorFunX.δAO_gap_bound
              (Hoff := Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff) X ≤ Goldbach.CanonParams.ε) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  have hBase : FiniteBaseUpTo 1_000_000 := Goldbach.FiniteBase.finiteBaseUpTo_1e6
  exact
    Goldbach.goldbach_from_tenorFunX_fun_autoHoff
      (hεlt := hεlt)
      (hBudget := by
        intro X N hX hN
        exact hBudget hX hN)
      (hBase := hBase)

end Goldbach

