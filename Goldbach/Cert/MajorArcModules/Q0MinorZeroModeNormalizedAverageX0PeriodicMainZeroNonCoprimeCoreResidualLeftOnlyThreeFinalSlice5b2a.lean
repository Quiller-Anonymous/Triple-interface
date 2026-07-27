import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalCommon
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalPartB2b2a

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

def PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2a : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.filter
    (fun p => ¬ leftOnlyThreeLexLe 4359 1453 p ∧ leftOnlyThreeLexLe 4614 1538 p)

def PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2a : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2a.filter
    (fun p => ! decide (p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2a))

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2a_card :
    PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2a.card = 0 := by
  native_decide

theorem PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2a_covered :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2a,
      p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2a := by
  exact leftOnlyThree_forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2a)
    (P := fun p => p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2a)
    (by
      simpa [PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2a]
        using PeriodicMainRecordsCoreLeftOnlyThreePayloadBadPairsSlice5b2a_card)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
