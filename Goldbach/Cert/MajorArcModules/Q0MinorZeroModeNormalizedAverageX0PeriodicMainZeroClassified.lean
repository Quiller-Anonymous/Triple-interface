import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverage
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicException
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroKnown

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def PeriodicMainZeroClassifiedPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroKnownPairs ∪ PeriodicMainZeroDyadicExceptionPairs

theorem PeriodicMainZeroClassifiedPairs_card :
    PeriodicMainZeroClassifiedPairs.card = 18870 := by
  native_decide

theorem PeriodicMainZeroClassifiedPairs_subset_zeroRecordPairs :
    PeriodicMainZeroClassifiedPairs ⊆ PeriodicMainZeroRecordPairs := by
  native_decide

theorem PeriodicMainZeroClassifiedPairs_eq_zeroRecordPairs :
    PeriodicMainZeroClassifiedPairs = PeriodicMainZeroRecordPairs := by
  apply Finset.eq_of_subset_of_card_le
    PeriodicMainZeroClassifiedPairs_subset_zeroRecordPairs
  rw [PeriodicMainZeroClassifiedPairs_card, PeriodicMainZeroRecordPairs_card]

theorem PeriodicMainZeroRecordPairs_eq_classifiedPairs :
    PeriodicMainZeroRecordPairs = PeriodicMainZeroClassifiedPairs := by
  exact PeriodicMainZeroClassifiedPairs_eq_zeroRecordPairs.symm

theorem PeriodicMainZeroRecordPairs_value_on_records_of_dyadicException
    (hdyadic :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0) :
    ∀ p ∈ PeriodicMainZeroRecordPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  have hpClassified : p ∈ PeriodicMainZeroClassifiedPairs := by
    rw [PeriodicMainZeroClassifiedPairs_eq_zeroRecordPairs]
    exact hp
  rw [PeriodicMainZeroClassifiedPairs] at hpClassified
  rcases Finset.mem_union.mp hpClassified with hpKnown | hpDyadic
  · exact PeriodicMainZeroKnown_value_on_records p hpKnown
  · exact hdyadic p hpDyadic

structure PeriodicMainDyadicExceptionZeroCertificateAtX0 : Prop where
  value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicException
    (cert : PeriodicMainDyadicExceptionZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp hnot
  exact PeriodicMainZeroRecordPairs_value_on_records_of_dyadicException
    cert.value_on_records p
    (PeriodicMainFullBlockExplicit_not_nonzero_mem_zero hp hnot)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
