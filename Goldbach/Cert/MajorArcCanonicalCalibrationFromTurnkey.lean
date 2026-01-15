import Goldbach.Cert.MajorArcModules.TurnkeyCanon

/-!
Offline helper: build a `CanonicalCalibration` datum from a turnkey/certified canonical major-arc bound.

This file introduces **no axioms**. It is intended to be used once a data-driven certificate
produces an inhabitant of `TurnkeyMajorArcCanon` (see `Goldbach/Cert/MajorArcCertChecker.lean`).

At that point, `Goldbach.Cert.MajorArcCanonicalCalibrationOffline.canonCalibration` can be
switched to use this construction instead of the pinned-boundary placeholder.
-/

namespace Goldbach.Cert.MajorArcCanonicalCalibrationFromTurnkey

open Goldbach.Cert.MajorArcCalibrationFunX
open Goldbach.Cert.MajorArcModules.TurnkeyCanon

noncomputable section

/-- Convert a turnkey/certified canonical on-window bound into a `CanonicalCalibration`. -/
noncomputable def canonCalibration (h : TurnkeyMajorArcCanon) : CanonicalCalibration :=
  canonCalibration_of_turnkey h

end

end Goldbach.Cert.MajorArcCanonicalCalibrationFromTurnkey
