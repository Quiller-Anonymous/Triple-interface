import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0BoundaryInactive
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailFinal

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem surrogateBoundary_X0_eq_fullCert_of_activeInactiveCertificates
    (hactive :
      surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat X0 =
        surrogateBoundaryX0ActiveSignedCert)
    (hinactive :
      surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryInactiveCorrectionRat X0 =
        surrogateBoundaryX0InactiveCorrectionCert) :
    surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryPairSumUpToQ0Rat X0 =
      surrogateBoundaryX0FullCert := by
  unfold surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryInactiveCorrectionRat at hinactive
  unfold surrogateBoundaryX0FullCert
  linarith

theorem centeredNormalizedSigmaTruncBoundaryRatCertificateAtX0_of_activeInactiveCertificates
    (hactive :
      CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0)
    (hinactive :
      CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0) :
    CenteredNormalizedSigmaTruncBoundaryRatCertificateAtX0 := by
  exact centeredNormalizedSigmaTruncBoundaryRatCertificateAtX0_of_eq_cert
    (surrogateBoundary_X0_eq_fullCert_of_activeInactiveCertificates hactive hinactive)

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMain
    (hchunk000_sub000 :
      (∑ q ∈ TailChunk000Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub000First5000)
    (hchunk000_sub001 :
      (∑ q ∈ TailChunk000Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk000Sub001First5000)
    (hchunk001_sub000 :
      (∑ q ∈ TailChunk001Sub000SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub000First5000)
    (hchunk001_sub001 :
      (∑ q ∈ TailChunk001Sub001SupportExplicit,
          surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q) =
        surrogateDiagTailX0RatChunk001Sub001First3211)
    (hactive :
      CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0)
    (hinactive :
      CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0)
    (hmain :
      surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0
        = surrogatePeriodicMainX0RatCert) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSumsAndRemainingAggregateCertificates
    hchunk000_sub000
    hchunk000_sub001
    hchunk001_sub000
    hchunk001_sub001
    hmain
    (surrogateBoundary_X0_eq_fullCert_of_activeInactiveCertificates hactive hinactive)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
