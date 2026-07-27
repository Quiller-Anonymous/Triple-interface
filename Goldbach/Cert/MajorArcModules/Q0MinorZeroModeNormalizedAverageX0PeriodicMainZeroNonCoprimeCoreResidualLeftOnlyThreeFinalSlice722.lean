import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk722

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice722 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 4746 113 p ∧ leftOnlyThreeLexLe 4746 226 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice722 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice722.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk722Pairs))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice722_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice722.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice722_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice722,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk722Pairs := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice722)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk722Pairs)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice722]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice722_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
