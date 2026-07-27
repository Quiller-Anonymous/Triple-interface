import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc721
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalSlice722

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_4746_226 :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      leftOnlyThreeLexLe 4746 226 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp h722
  by_cases h721 : leftOnlyThreeLexLe 4746 113 p
  · exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_upTo_4746_113
        p hp h721
  · exact PeriodicMainRecordsCoreLeftOnlyThreeChunk722_value_on_records p
      (PeriodicMainRecordsCoreLeftOnlyThreeTargetSlice722_covered p
        (Finset.mem_filter.mpr ⟨hp, h721, h722⟩))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
