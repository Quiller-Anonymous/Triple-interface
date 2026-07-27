import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc5b2a
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalSlice5b2b1

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_4737_1579 :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      leftOnlyThreeLexLe 4737 1579 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp h5b2b1
  by_cases h5b2a : leftOnlyThreeLexLe 4614 1538 p
  · exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_4614_1538
        p hp h5b2a
  · exact PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b1_value_on_records p
      (PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice5b2b1_covered p
        (Finset.mem_filter.mpr ⟨hp, h5b2a, h5b2b1⟩))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
