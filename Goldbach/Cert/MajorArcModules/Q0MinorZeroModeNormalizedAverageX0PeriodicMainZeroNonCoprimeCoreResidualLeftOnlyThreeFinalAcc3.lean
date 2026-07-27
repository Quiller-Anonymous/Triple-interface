import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc2
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalSlice3

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_678_10 :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      leftOnlyThreeLexLe 678 10 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp h3
  by_cases h2 : leftOnlyThreeLexLe 258 34 p
  · exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_258_34
        p hp h2
  · exact PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB0_value_on_records p
      (PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice3_covered p
        (Finset.mem_filter.mpr ⟨hp, h2, h3⟩))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
