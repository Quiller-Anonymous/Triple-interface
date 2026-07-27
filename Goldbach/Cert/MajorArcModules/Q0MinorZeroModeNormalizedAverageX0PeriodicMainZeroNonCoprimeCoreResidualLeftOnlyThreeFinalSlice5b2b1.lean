import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalPartB2b2b1

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b1 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 4614 1538 p ∧ leftOnlyThreeLexLe 4737 1579 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b1 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b1.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b1))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b1_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b1.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b1_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b1,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b1 := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b1)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b1)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b1]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b1_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
