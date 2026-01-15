import Goldbach.Cert.MajorArcCertChecker
import Goldbach.Cert.MajorArcModules.TurnkeyCanon
import Goldbach.Cert.MajorArcCanonicalCalibrationFromTurnkey

/-!
Turnkey major-arc certificate interface.

This file keeps the “certificate ⇒ turnkey bound” plumbing separate from any generated artifacts.

Workflow:
* A generator produces a `Cert` (purely rational inequalities) and a proof `cert.Valid` via
  `native_decide`.
* A handwritten reduction lemma turns `cert.Valid` into `TurnkeyMajorArcCanon`.
* This file packages that pair as `MajorArcCertificate` and exposes the downstream constructions
  (canonical calibration and inner-swap instance) without introducing axioms.
-/

namespace Goldbach.Cert.MajorArcCertificate

open Goldbach.Cert.MajorArcModules.TurnkeyCanon
open Goldbach.Cert.MajorArcCanonicalCalibrationFromTurnkey

/-- A turnkey major-arc certificate: data + reduction proof. -/
structure Certificate where
  cert : Goldbach.Cert.MajorArcCertChecker.Cert
  eval : cert.Valid → TurnkeyMajorArcCanon

namespace Certificate

/-- Build a `TurnkeyMajorArcCanon` from a verified certificate. -/
def turnkey (C : Certificate) (hvalid : C.cert.Valid) : TurnkeyMajorArcCanon :=
  C.eval hvalid

/-- Build a `CanonicalCalibration` datum from a verified certificate. -/
noncomputable def calibration (C : Certificate) (hvalid : C.cert.Valid) :
    Goldbach.Cert.MajorArcCalibrationFunX.CanonicalCalibration :=
  Goldbach.Cert.MajorArcCanonicalCalibrationFromTurnkey.canonCalibration (C.eval hvalid)

/-- Pipeline-facing inner-swap instance obtained from a verified certificate. -/
noncomputable def innerSwapOnWindow (C : Certificate) (hvalid : C.cert.Valid) :
    Goldbach.ParallelTenorFunX.InnerSwapOnWindow :=
  Goldbach.Cert.MajorArcModules.TurnkeyCanon.innerSwapOnWindow_of_turnkey (C.eval hvalid)

end Certificate

end Goldbach.Cert.MajorArcCertificate
