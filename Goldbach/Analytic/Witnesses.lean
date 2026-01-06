import Mathlib
import Goldbach.ParallelTenorFunX
import Goldbach.AO_OffDiag.TenorHypFunX_Canon

/-!
Canonical witness export (Goldbach track).

This module re-exports the *parallel FunX* witness from `Goldbach.ParallelTenorFunX`,
since that is the paper-faithful pipeline.

It is parameterized by the remaining explicit hypotheses:
* a major-arc swap bound on the window (`InnerSwapOnWindow`),
* the BG weights-bridge hypothesis (`WeightsBridgeHyp`),
* the numeric gap/budget inequality on the window (`hBudget`),
* and the positivity margin `ε < c0` (`hεlt`).
-/

namespace Goldbach.Analytic

open Goldbach
open Goldbach.Windows

/-- Canonical OffDiag hypothesis for the FunX track. -/
noncomputable abbrev HoffCanon : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp :=
  Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff

/-- Canonical closure constant for the FunX track: `c0 = cAO(caps HoffCanon)`. -/
noncomputable abbrev c0Canon : ℝ :=
  Goldbach.ParallelTenorFunX.c0 HoffCanon

/-- Canonical witness for the Goldbach pipeline (parallel FunX track). -/
noncomputable def witnessCanonical
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.ParallelTenorFunX.InnerSwapOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hεlt : (0.01 : ℝ) < c0Canon)
    (hBudget :
      ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ Goldbach.Windows.EvenIn X (10_000 : ℕ) →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := HoffCanon) ≤ (0.01 : ℝ)) :
    Goldbach.Analytic.PointwiseWitness :=
  Goldbach.ParallelTenorFunX.witness_funX
    (Hoff := HoffCanon) (hεlt := hεlt) (hBudget := hBudget)

end Goldbach.Analytic

