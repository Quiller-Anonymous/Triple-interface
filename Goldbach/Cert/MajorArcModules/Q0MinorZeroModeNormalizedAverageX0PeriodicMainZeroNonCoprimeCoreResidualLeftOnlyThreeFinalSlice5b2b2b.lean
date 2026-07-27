import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalPartB2b2b2b

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b2b : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 4746 113 p ∧ leftOnlyThreeLexLe 4746 1582 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b2b : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b2b.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2b))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b2b_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b2b.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b2b_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b2b,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2b := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b2b)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2b)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b2b]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2b2b_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
