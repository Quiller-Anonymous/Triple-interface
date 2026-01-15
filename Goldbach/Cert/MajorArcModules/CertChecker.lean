import Goldbach.Cert.MajorArcCertChecker

/-!
`MajorArcModules/CertChecker` re-exports the data-driven major-arc certificate checker scaffolding.

This is part of the offline `MajorArcModules` staging area and is not imported by the live
Goldbach pipeline.
-/

namespace Goldbach.Cert.MajorArcModules.CertChecker

export Goldbach.Cert.MajorArcCertChecker
  (CheckLE Cert CheckLE.Holds Cert.Valid empty_valid)

end Goldbach.Cert.MajorArcModules.CertChecker
