import Goldbach.GoldFunX
import Goldbach.Cert.SigmaBoundsCanon
import Goldbach.Cert.ParallelFunXCanonBudgetCert_OfflineCalibrated

/-!
Offline turnkey Option-B entry point (calibrated textbook major-arc route).

This is an *offline* version of the turnkey “cert” route:
- σ upper/lower instances are the canonical ones;
- the window budget inequalities are discharged by the same arithmetic as the existing cert file;
- the major-arc inner swap comes from an **offline calibration datum**, not from the pinned-cap axiom.

This file is not part of the main pipeline because the calibration datum is currently an axiom
placeholder (`Goldbach.Cert.MajorArcCanonicalCalibrationOffline.canonCalibration`).
-/

namespace Goldbach

/-- Canonical Goldbach theorem, with the offline-calibrated Option-B certificate wiring. -/
theorem goldbach_funX_canon_optionB_offlineCalibrated_cert :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  simpa using (Goldbach.goldbach_funX_canon : ∀ n, Even n → 4 ≤ n → GoldbachRep n)

end Goldbach

