-- Goldbach/GoldFunX_Pinned.lean
--
-- Convenience entry point: close the remaining hypotheses of `Goldbach.goldbach_funX_canon`
-- using the current pinned major-arc calibration datum and the axiom-free bridge stub.

import Goldbach.GoldFunX
import Goldbach.Cert.MajorArcCanonCalibrationFromPinned
import Goldbach.Cert.SigmaBoundsCanon
import Goldbach.BG_CalibBridgeStub

namespace Goldbach

/--
Canonical end-to-end Goldbach theorem, using the current pinned major-arc calibration datum.

This is a “silver build” convenience wrapper: it depends on the project-specific axiom
`Goldbach.Cert.MajorArcCanonCalibrationFromPinned.canonCalibration`.
-/
theorem goldbach_funX_canon_pinned
    (hεlt :
      ∀ {X : ℕ}, Goldbach.ParallelTenorFunX.X0 ≤ X →
        Goldbach.CanonParams.ε <
          Goldbach.ParallelFunXCanonScale.c0 X)
    (hBudget :
      ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ Goldbach.Windows.EvenIn X (10_000 : ℕ) →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + @Goldbach.ParallelTenorFunX.δAO_gap_bound
              (Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_canonCalibration
                Goldbach.Cert.MajorArcCanonCalibrationFromPinned.canonCalibration)
              Goldbach.ParallelFunXCanonScale.Hoff X ≤ Goldbach.CanonParams.ε) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  -- `BG_CalibBridgeStub` supplies the (axiom-free) `WeightsBridgeHyp` instance.
  exact
    goldbach_funX_canon_of_canonCalibration
      Goldbach.Cert.MajorArcCanonCalibrationFromPinned.canonCalibration
      hεlt
      hBudget

end Goldbach
