import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0BoundaryCertificates
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailFinal

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem surrogateBoundary_X0_eq_fullExactCert_of_activeInactiveCertificates
    (hactive :
      surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat X0 =
        surrogateBoundaryX0ActiveSignedExactCert)
    (hinactive :
      surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryInactiveCorrectionRat X0 =
        surrogateBoundaryX0InactiveCorrectionExactCert) :
    surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryPairSumUpToQ0Rat X0 =
      surrogateBoundaryX0FullExactCert := by
  unfold surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryInactiveCorrectionRat at hinactive
  unfold surrogateBoundaryX0FullExactCert
  linarith

theorem abs_surrogateBoundary_X0_le_26_of_activeInactiveCertificates
    (hactive :
      CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0)
    (hinactive :
      CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0) :
    |surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryPairSumUpToQ0 X0|
      ≤ 26 := by
  exact abs_surrogateBoundary_X0_le_26_from_exact_cert
    (surrogateBoundary_X0_eq_fullExactCert_of_activeInactiveCertificates hactive hinactive)

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
  apply centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_surrogateNumericBounds
  · exact surrogateDiagonalMain_X0_le_36326
  · exact surrogateDiagonalSmallRest_X0_le_1207
  · exact surrogateDiagonalTail_X0_le_100_of_exact_rat_certificate
      (centeredNormalizedSigmaTruncSurrogateDiagonalTailExactRatCertificateAtX0_of_generatedSubchunkSums
        hchunk000_sub000 hchunk000_sub001 hchunk001_sub000 hchunk001_sub001)
      centeredNormalizedSigmaTruncSurrogateDiagonalTailExactRatCheckCertificateAtX0_true
  · exact abs_surrogatePeriodicMain_X0_le_37603_of_exactChecked_certificate
      (centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_exactCertificate
        (centeredNormalizedSigmaTruncSurrogatePeriodicMainExactRatCertificateAtX0_of_eq_cert hmain))
  · exact abs_surrogateBoundary_X0_le_26_of_activeInactiveCertificates hactive hinactive

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
