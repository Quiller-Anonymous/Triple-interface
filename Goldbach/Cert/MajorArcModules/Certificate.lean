import Goldbach.Cert.MajorArcCertificate

/-!
`MajorArcModules/Certificate` provides convenient aliases to the turnkey certificate interface,
avoiding namespace shadowing warnings while keeping the offline bundle easy to use.
-/

namespace Goldbach.Cert.MajorArcModules.Certificate

abbrev Certificate := Goldbach.Cert.MajorArcCertificate.Certificate
abbrev cert (C : Certificate) := C.cert
abbrev eval (C : Certificate) := C.eval

abbrev turnkey (C : Certificate) (hvalid : C.cert.Valid) :
    Goldbach.Cert.MajorArcModules.TurnkeyCanon.TurnkeyMajorArcCanon :=
  Goldbach.Cert.MajorArcCertificate.Certificate.turnkey C hvalid

noncomputable abbrev calibration (C : Certificate) (hvalid : C.cert.Valid) :
    Goldbach.Cert.MajorArcCalibrationFunX.CanonicalCalibration :=
  Goldbach.Cert.MajorArcCertificate.Certificate.calibration C hvalid

noncomputable abbrev innerSwapOnWindow (C : Certificate) (hvalid : C.cert.Valid) :
    Goldbach.ParallelTenorFunX.InnerSwapOnWindow :=
  Goldbach.Cert.MajorArcCertificate.Certificate.innerSwapOnWindow C hvalid

end Goldbach.Cert.MajorArcModules.Certificate
