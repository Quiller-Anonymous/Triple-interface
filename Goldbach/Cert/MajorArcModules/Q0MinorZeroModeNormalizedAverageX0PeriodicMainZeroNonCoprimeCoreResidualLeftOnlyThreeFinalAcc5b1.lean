import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc5a
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalSlice5b1

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

opaque PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_4359_1453 :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      leftOnlyThreeLexLe 4359 1453 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp h5b1
  by_cases h5a : leftOnlyThreeLexLe 3414 1138 p
  · exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_3414_1138
        p hp h5a
  · exact PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b1_value_on_records p
      (PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b1_covered p
        (Finset.mem_filter.mpr ⟨hp, h5a, h5b1⟩))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
