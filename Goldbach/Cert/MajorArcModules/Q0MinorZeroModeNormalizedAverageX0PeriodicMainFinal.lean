import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0BoundaryFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSumsAndFinalCertificates
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
    (hboundary_active :
      CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0)
    (hboundary_inactive :
      CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0)
    (hmain :
      CenteredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_tailChunkEqualitiesAndRemainingAggregateCertificates
    (surrogateDiagTailChunk000_mainSupport_sum_eq_cert hchunk000_sub000 hchunk000_sub001)
    (surrogateDiagTailChunk001_mainSupport_sum_eq_cert hchunk001_sub000 hchunk001_sub001)
    hmain
    (centeredNormalizedSigmaTruncBoundaryRatCertificateAtX0_of_activeInactiveCertificates
      hboundary_active hboundary_inactive)

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainEq
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
    (hboundary_active :
      CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0)
    (hboundary_inactive :
      CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0)
    (hmain :
      surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0
        = surrogatePeriodicMainX0RatCert) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSumsAndFinalCertificates
    hchunk000_sub000
    hchunk000_sub001
    hchunk001_sub000
    hchunk001_sub001
    hboundary_active
    hboundary_inactive
    (centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_eq_cert hmain)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
