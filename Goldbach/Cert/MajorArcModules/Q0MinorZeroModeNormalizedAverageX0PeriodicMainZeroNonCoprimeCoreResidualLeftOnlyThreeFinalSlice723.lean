import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk723

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice723 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 4746 226 p ∧ leftOnlyThreeLexLe 4746 791 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice723 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice723.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk723Pairs))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice723_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice723.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice723_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice723,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk723Pairs := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice723)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk723Pairs)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice723]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice723_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
