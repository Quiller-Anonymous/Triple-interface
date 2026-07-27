import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk719

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice719 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 4737 1579 p ∧ leftOnlyThreeLexLe 4746 7 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice719 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice719.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk719Pairs))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice719_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice719.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice719_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice719,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk719Pairs := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice719)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk719Pairs)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice719]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice719_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
