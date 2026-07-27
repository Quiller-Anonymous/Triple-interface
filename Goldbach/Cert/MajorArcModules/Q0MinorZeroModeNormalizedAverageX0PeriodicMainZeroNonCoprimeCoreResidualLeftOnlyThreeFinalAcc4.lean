import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc3
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalSlice4

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_2307_1538 :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      leftOnlyThreeLexLe 2307 1538 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp h4
  by_cases h3 : leftOnlyThreeLexLe 678 10 p
  · exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_678_10
        p hp h3
  · exact PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB1_value_on_records p
      (PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice4_covered p
        (Finset.mem_filter.mpr ⟨hp, h3, h4⟩))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
