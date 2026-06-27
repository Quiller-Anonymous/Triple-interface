import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0BoundaryActive

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable def surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryInactiveCorrectionRat
    (X : ℕ) : ℚ :=
  surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryPairSumUpToQ0Rat X
    - surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat X

def CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryInactiveCorrectionRat X0 =
    surrogateBoundaryX0InactiveCorrectionExactCert

theorem centeredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0_of_eq_cert
    (hcert :
      surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryInactiveCorrectionRat X0 =
        surrogateBoundaryX0InactiveCorrectionExactCert) :
    CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0 := by
  unfold CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0
  exact hcert

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
