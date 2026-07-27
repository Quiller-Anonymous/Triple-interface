import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc4
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalSlice5a

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_3414_1138 :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      leftOnlyThreeLexLe 3414 1138 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp h5a
  by_cases h4 : leftOnlyThreeLexLe 2307 1538 p
  · exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_2307_1538
        p hp h4
  · exact PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2a_value_on_records p
      (PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5a_covered p
        (Finset.mem_filter.mpr ⟨hp, h4, h5a⟩))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
