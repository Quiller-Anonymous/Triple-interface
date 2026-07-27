import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalSlice0

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_42_146 :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      leftOnlyThreeLexLe 42 146 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp h0
  exact PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA0_value_on_records p
    (PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice0_covered p
      (Finset.mem_filter.mpr ⟨hp, h0⟩))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
