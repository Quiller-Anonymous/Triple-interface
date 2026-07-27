import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalPartB1

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice4 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice4.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB1))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice4_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice4.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice4_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice4,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB1 := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice4)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB1)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice4]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice4_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
