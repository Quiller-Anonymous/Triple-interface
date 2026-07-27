import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc5b1
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalSlice5b2a

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_4614_1538 :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      leftOnlyThreeLexLe 4614 1538 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp h5b2a
  by_cases h5b1 : leftOnlyThreeLexLe 4359 1453 p
  · exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_4359_1453
        p hp h5b1
  · exact PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2a_value_on_records p
      (PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2a_covered p
        (Finset.mem_filter.mpr ⟨hp, h5b1, h5b2a⟩))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
