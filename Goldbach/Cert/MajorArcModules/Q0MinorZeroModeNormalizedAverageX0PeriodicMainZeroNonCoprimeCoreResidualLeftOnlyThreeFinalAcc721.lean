import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc720
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalSlice721

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_4746_113 :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      leftOnlyThreeLexLe 4746 113 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp h721
  by_cases h720 : leftOnlyThreeLexLe 4746 14 p
  · exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_4746_14
        p hp h720
  · exact PeriodicMainRecordsCoreLeftOnlyThreeChunk721_value_on_records p
      (PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice721_covered p
        (Finset.mem_filter.mpr ⟨hp, h720, h721⟩))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
