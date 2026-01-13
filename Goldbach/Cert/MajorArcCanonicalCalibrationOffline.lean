import Goldbach.Cert.MajorArcCanonCalibrationFromPinned

/-!
Offline placeholder: canonical major-arc calibration datum.

This module is **not** part of the main pipeline. It exists to support an “offline turnkey” route
that will eventually become fully proved/certified:

- A `CanonicalCalibration` datum packages:
  * a theorem-shaped major-arc bound `C/(log X)^A` on the canonical window, and
  * a project-specific calibration inequality turning it into the pinned cap `δ_major_canon`.

At the moment, supplying this datum is the remaining missing piece to make the Option-B turnkey
route gold-grade (no project-shaped major-arc axiom).  The intent is to replace the axiom below by
either:
- a proof from conventional analytic inputs plus explicit constants, or
- a checkable numerical certificate + Lean verification.
-/

namespace Goldbach.Cert.MajorArcCanonicalCalibrationOffline

open Goldbach.Cert.MajorArcCalibrationFunX

noncomputable section

/--
Offline calibration datum.

This is *not* part of the main pipeline. It is currently provided by the “pinned calibration
boundary” `MajorArcCanonCalibrationFromPinned`, which fixes explicit parameters `(A_canon,C_canon)`
and proves the numeric cutoff inequality; the remaining analytic major-arc bound at those
parameters is still an axiom.

Long-term goal: replace that axiom by a proof/certificate.
-/
noncomputable abbrev canonCalibration : CanonicalCalibration :=
  Goldbach.Cert.MajorArcCanonCalibrationFromPinned.canonCalibration

end

end Goldbach.Cert.MajorArcCanonicalCalibrationOffline
