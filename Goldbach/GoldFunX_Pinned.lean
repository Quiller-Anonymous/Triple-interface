-- Goldbach/GoldFunX_Pinned.lean
--
-- Convenience entry point: close the remaining hypotheses of `Goldbach.goldbach_funX_canon`
-- using the current pinned major-arc calibration datum and the axiom-free bridge stub.

import Goldbach.GoldFunX
import Goldbach.Cert.MajorArcCanonCalibrationFromPinned
import Goldbach.BG_CalibBridgeStub

namespace Goldbach

/--
Canonical end-to-end Goldbach theorem, using the current pinned major-arc calibration datum.

This is a “silver build” convenience wrapper: it depends on the project-specific axiom
`Goldbach.Cert.MajorArcCanonCalibrationFromPinned.canonCalibration`.
-/
theorem goldbach_funX_canon_pinned :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  -- `BG_CalibBridgeStub` supplies the (axiom-free) `WeightsBridgeHyp` instance.
  exact
    goldbach_funX_canon_of_canonCalibration
      Goldbach.Cert.MajorArcCanonCalibrationFromPinned.canonCalibration

end Goldbach

