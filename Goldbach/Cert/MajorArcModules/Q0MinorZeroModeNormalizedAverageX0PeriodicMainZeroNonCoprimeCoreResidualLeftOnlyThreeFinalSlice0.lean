import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalPartA0

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice0 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice0.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA0))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice0_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice0.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice0_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice0,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA0 := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice0)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA0)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice0]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice0_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
