import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroRightColumns

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/--
Reduced theorem surface for dyadic-exception zero records.

The unit rows, coprime `3`/`6` rows, and coprime right-column `3`/`6` records
are now structural. The non-coprime records are kept split by left `3`/`6`,
right `3`/`6`, and the deeper residual so later payload generation or
structural work does not target one undifferentiated mass.
-/
structure PeriodicMainDyadicExceptionReducedZeroCertificateAtX0 : Prop where
  coprime_core_residual_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeCoreResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_rowThreeSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_residual_rightThreeSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_core_residual_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainDyadicExceptionSplitZeroCertificateAtX0_of_reduced
    (cert : PeriodicMainDyadicExceptionReducedZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionSplitZeroCertificateAtX0 := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionCoprimePairs_eq_rowThreeSix_union_residual] at hp
    rcases Finset.mem_union.mp hp with hpRow | hpResidual
    · exact PeriodicMainZeroDyadicExceptionCoprimeRowThreeSix_value_on_records_public p hpRow
    · rw [PeriodicMainZeroDyadicExceptionCoprimeResidualPairs_eq_rightThreeSix_union_core] at hpResidual
      rcases Finset.mem_union.mp hpResidual with hpRight | hpCore
      · exact PeriodicMainZeroDyadicExceptionCoprimeResidualRightThreeSix_value_on_records_public p hpRight
      · exact cert.coprime_core_residual_value_on_records p hpCore
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionNonCoprimePairs_eq_rowThreeSix_union_residual] at hp
    rcases Finset.mem_union.mp hp with hpRow | hpResidual
    · exact cert.nonCoprime_rowThreeSix_value_on_records p hpRow
    · rw [PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs_eq_rightThreeSix_union_core] at hpResidual
      rcases Finset.mem_union.mp hpResidual with hpRight | hpCore
      · exact cert.nonCoprime_residual_rightThreeSix_value_on_records p hpRight
      · exact cert.nonCoprime_core_residual_value_on_records p hpCore

theorem PeriodicMainDyadicExceptionZeroCertificateAtX0_of_reduced
    (cert : PeriodicMainDyadicExceptionReducedZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionZeroCertificateAtX0 :=
  PeriodicMainDyadicExceptionZeroCertificateAtX0_of_split
    (PeriodicMainDyadicExceptionSplitZeroCertificateAtX0_of_reduced cert)

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicExceptionReduced
    (cert : PeriodicMainDyadicExceptionReducedZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  exact PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicException
    (PeriodicMainDyadicExceptionZeroCertificateAtX0_of_reduced cert)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
