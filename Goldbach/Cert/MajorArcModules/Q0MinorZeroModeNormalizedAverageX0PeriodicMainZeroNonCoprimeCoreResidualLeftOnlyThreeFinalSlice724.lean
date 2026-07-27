import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk724

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice724 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 4746 791 p ∧ leftOnlyThreeLexLe 4746 1582 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice724 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice724.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk724Pairs))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice724_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice724.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice724_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice724,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk724Pairs := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice724)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk724Pairs)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice724]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice724_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
