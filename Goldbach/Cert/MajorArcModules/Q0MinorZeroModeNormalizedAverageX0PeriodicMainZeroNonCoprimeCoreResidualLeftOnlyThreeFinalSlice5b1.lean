import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalPartB2b1

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b1 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 3414 1138 p ∧ leftOnlyThreeLexLe 4359 1453 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b1 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b1.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b1))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b1_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b1.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b1_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b1,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b1 := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b1)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b1)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b1]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b1_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
