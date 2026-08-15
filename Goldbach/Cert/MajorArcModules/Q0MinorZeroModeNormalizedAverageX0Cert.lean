import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualFinal

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/--
Top-level Route A integration surface.

This keeps the still-external payload certificates explicit while forcing the
tail, boundary, periodic-main, and final numeric wrapper APIs to typecheck
together in one module.
-/
theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_routeA_remaining_certificates
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
    (periodicMainValue : ℕ × ℕ → ℚ)
    (hvalue :
      ∀ p ∈ PeriodicMainNonzeroRecordPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = periodicMainValue p)
    (hsum :
      (∑ p ∈ PeriodicMainNonzeroRecordPairs, periodicMainValue p) =
        surrogatePeriodicMainX0RatCert) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact
    centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainCommonFactorSurfaces
      hchunk000_sub000
      hchunk000_sub001
      hchunk001_sub000
      hchunk001_sub001
      hboundary_active
      hboundary_inactive
      periodicMainValue
      hvalue
      hsum
      PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0_certified

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_routeA_tail_and_boundary_certificates
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
      CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact
    centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSumsAndFinalCertificates
      hchunk000_sub000
      hchunk000_sub001
      hchunk001_sub000
      hchunk001_sub001
      hboundary_active
      hboundary_inactive
      centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_certified

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
