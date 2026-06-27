import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0BoundaryPayload

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable def BoundaryActiveSupportExplicit : Finset ℕ :=
  normalizedSigmaTruncSummandCoeffSupportUpToQ0.filter
    (fun q => q ≤ (H + 1) / 2)

noncomputable def surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat
    (X : ℕ) : ℚ :=
  ∑ q ∈ BoundaryActiveSupportExplicit,
    ∑ q' ∈ BoundaryActiveSupportExplicit,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * surrogateCenteredRamanujanPairPeriodicBoundaryTermRat X q q'

def CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat X0 =
    surrogateBoundaryX0ActiveSignedExactCert

theorem centeredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0_of_eq_cert
    (hcert :
      surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat X0 =
        surrogateBoundaryX0ActiveSignedExactCert) :
    CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0 := by
  unfold CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0
  exact hcert

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
