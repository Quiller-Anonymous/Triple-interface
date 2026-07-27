import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk720

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice720 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 4746 7 p ∧ leftOnlyThreeLexLe 4746 14 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice720 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice720.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk720Pairs))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice720_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice720.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice720_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice720,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk720Pairs := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice720)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreeChunk720Pairs)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice720]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice720_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
