import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0BoundaryFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainReducedSparse
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowAssembly
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidual
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeRightThreeSixCertificate
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeRowThreeSixCertificate

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
  apply centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_surrogateNumericBounds
  · exact surrogateDiagonalMain_X0_le_36326
  · exact surrogateDiagonalSmallRest_X0_le_1207
  · exact surrogateDiagonalTail_X0_le_100_of_exact_rat_certificate
      (centeredNormalizedSigmaTruncSurrogateDiagonalTailExactRatCertificateAtX0_of_generatedSubchunkSums
        hchunk000_sub000 hchunk000_sub001 hchunk001_sub000 hchunk001_sub001)
      centeredNormalizedSigmaTruncSurrogateDiagonalTailExactRatCheckCertificateAtX0_true
  · exact abs_surrogatePeriodicMain_X0_le_37603_of_exactChecked_certificate hmain
  · exact abs_surrogateBoundary_X0_le_26_of_activeInactiveCertificates
      hboundary_active hboundary_inactive

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

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainRows
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
    (hpm :
      PeriodicMainRowSliceSumCertificateAtX0) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainEq
    hchunk000_sub000
    hchunk000_sub001
    hchunk001_sub000
    hchunk001_sub001
    hboundary_active
    hboundary_inactive
    (periodicMainCert_true_of_rowSliceCertificate hpm)

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainRemainingRows
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
    (hpm :
      PeriodicMainRowSliceRemainingCertificateAtX0) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainEq
    hchunk000_sub000
    hchunk000_sub001
    hchunk001_sub000
    hchunk001_sub001
    hboundary_active
    hboundary_inactive
    (periodicMainCert_true_of_remainingRowSliceCertificate hpm)

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainSparse
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
    (hpm :
      PeriodicMainSparseOrderedCertificateAtX0) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSumsAndFinalCertificates
    hchunk000_sub000
    hchunk000_sub001
    hchunk001_sub000
    hchunk001_sub001
    hboundary_active
    hboundary_inactive
    (centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_sparseOrderedCertificate hpm)

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainNonzeroReducedSparse
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
    (hpm :
      PeriodicMainNonzeroReducedSparseCertificateAtX0 periodicMainValue) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSumsAndFinalCertificates
    hchunk000_sub000
    hchunk000_sub001
    hchunk001_sub000
    hchunk001_sub001
    hboundary_active
    hboundary_inactive
    (centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_nonzeroReducedSparse
      periodicMainValue hpm)

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainCommonFactorSurfaces
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
        surrogatePeriodicMainX0RatCert)
    (coreCert : PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0) :
    CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795 := by
  exact centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainNonzeroReducedSparse
    hchunk000_sub000
    hchunk000_sub001
    hchunk001_sub000
    hchunk001_sub001
    hboundary_active
    hboundary_inactive
    periodicMainValue
    ⟨hvalue, hsum,
      PeriodicMainDyadicExceptionReducedZeroCertificateAtX0_of_nonCoprimeReduced
        (PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_commonFactorSurfaces
          PeriodicMainDyadicExceptionNonCoprimeRowThreeSixCommonFactorZeroCertificateAtX0_of_remaining
          PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0_of_transport
          coreCert)⟩

theorem centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_generatedTailSubchunkSums_boundaryActiveInactiveAndPeriodicMainCertifiedCommonFactorSurfaces
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

theorem periodicMainNonzeroReducedSparseCertificateAtX0_certified :
    PeriodicMainNonzeroReducedSparseCertificateAtX0 periodicMainNonzeroActualValue := by
  refine ⟨periodicMainNonzeroActualValue_on_records,
    periodicMainNonzeroActualValue_sum_eq_cert, ?_⟩
  exact
    PeriodicMainDyadicExceptionReducedZeroCertificateAtX0_of_nonCoprimeReduced
      (PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_commonFactorSurfaces
        PeriodicMainDyadicExceptionNonCoprimeRowThreeSixCommonFactorZeroCertificateAtX0_of_remaining
        PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0_of_transport
        PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0_certified)

theorem periodicMainCert_true_of_nonzeroFinal :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0 =
      surrogatePeriodicMainX0RatCert := by
  exact periodicMainCert_true_of_nonzeroReducedSparseCertificate
    periodicMainNonzeroActualValue
    periodicMainNonzeroReducedSparseCertificateAtX0_certified

theorem centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_certified :
    CenteredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0 := by
  exact centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_nonzeroReducedSparse
    periodicMainNonzeroActualValue
    periodicMainNonzeroReducedSparseCertificateAtX0_certified

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
