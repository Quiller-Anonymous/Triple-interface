import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailChunk001

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem surrogateDiagonalTailChunkedRat_X0_eq_of_generatedSubchunkSums
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
        surrogateDiagTailX0RatChunk001Sub001First3211) :
    surrogateCenteredNormalizedSigmaTruncDiagonalEnergyDirectTailRat X0 =
      surrogateDiagTailX0RatChunk000 + surrogateDiagTailX0RatChunk001 := by
  simpa [CenteredNormalizedSigmaTruncSurrogateDiagonalTailChunkedRatCertificateAtX0] using
    centeredNormalizedSigmaTruncSurrogateDiagonalTailChunkedRatCertificateAtX0_of_support_and_chunkCertificates
      centeredNormalizedSigmaTruncSurrogateDiagonalTailChunkSupportCertificateAtX0_true
      (centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk000RatCertificateAtX0_of_eq_cert
        (surrogateDiagTailChunk000_mainSupport_sum_eq_cert hchunk000_sub000 hchunk000_sub001))
      (centeredNormalizedSigmaTruncSurrogateDiagonalTailChunk001RatCertificateAtX0_of_eq_cert
        (surrogateDiagTailChunk001_mainSupport_sum_eq_cert hchunk001_sub000 hchunk001_sub001))

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailChunkedRatCertificateAtX0_of_generatedSubchunkSums
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
        surrogateDiagTailX0RatChunk001Sub001First3211) :
    CenteredNormalizedSigmaTruncSurrogateDiagonalTailChunkedRatCertificateAtX0 := by
  exact centeredNormalizedSigmaTruncSurrogateDiagonalTailChunkedRatCertificateAtX0_of_eq_cert
    (surrogateDiagonalTailChunkedRat_X0_eq_of_generatedSubchunkSums
      hchunk000_sub000 hchunk000_sub001 hchunk001_sub000 hchunk001_sub001)

theorem centeredNormalizedSigmaTruncSurrogateDiagonalTailExactRatCertificateAtX0_of_generatedSubchunkSums
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
        surrogateDiagTailX0RatChunk001Sub001First3211) :
    CenteredNormalizedSigmaTruncSurrogateDiagonalTailExactRatCertificateAtX0 := by
  exact centeredNormalizedSigmaTruncSurrogateDiagonalTailExactRatCertificateAtX0_of_chunked_sum
    (surrogateDiagonalTailChunkedRat_X0_eq_of_generatedSubchunkSums
      hchunk000_sub000 hchunk000_sub001 hchunk001_sub000 hchunk001_sub001)

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSumsAndRemainingAggregateCertificates
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
    (hmain :
      surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0
        = surrogatePeriodicMainX0RatCert)
    (hboundary :
      surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryPairSumUpToQ0Rat X0
        = surrogateBoundaryX0FullCert) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_tailChunkEqualitiesAndRemainingAggregateCertificates
    (surrogateDiagTailChunk000_mainSupport_sum_eq_cert hchunk000_sub000 hchunk000_sub001)
    (surrogateDiagTailChunk001_mainSupport_sum_eq_cert hchunk001_sub000 hchunk001_sub001)
    (centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_exactCertificate
      (centeredNormalizedSigmaTruncSurrogatePeriodicMainExactRatCertificateAtX0_of_eq_cert hmain))
    (centeredNormalizedSigmaTruncBoundaryRatCertificateAtX0_of_eq_cert hboundary)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
