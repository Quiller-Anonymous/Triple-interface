import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk721

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice721 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 4746 14 p ∧ leftOnlyThreeLexLe 4746 113 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice721 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice721.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk721Pairs))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice721_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice721.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice721_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice721,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk721Pairs := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice721)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk721Pairs)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice721]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice721_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
