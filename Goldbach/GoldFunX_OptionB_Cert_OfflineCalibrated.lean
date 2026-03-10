import Goldbach.GoldFunX
import Goldbach.Cert.SigmaBoundsCanon

/-!
Offline Option-B entry point (calibrated textbook major-arc route).

This is an *offline* version of the scale-sensitive Option-B route:
- σ upper/lower instances are the canonical ones;
- the window budget inequalities are expected through the scale-sensitive
  `ParallelFunXCanonScale.BudgetHyp` bundle;
- the major-arc inner swap comes from an **offline calibration datum**, not from the pinned-cap axiom.

This file is not part of the main pipeline because the calibration datum is currently an axiom
placeholder (`Goldbach.Cert.MajorArcCanonicalCalibrationOffline.canonCalibration`).
-/

namespace Goldbach

/-- Canonical Goldbach theorem, with the offline-calibrated scale-sensitive budget bundled as an instance. -/
theorem goldbach_funX_canon_optionB_offlineCalibrated_cert
    [Goldbach.ParallelFunXCanonScale.BudgetHyp] :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  simpa using (Goldbach.goldbach_funX_canon : ∀ n, Even n → 4 ≤ n → GoldbachRep n)

end Goldbach
