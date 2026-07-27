import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk719
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk720
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk721

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2a : Finset (ℕ × ℕ) :=
  ((PeriodicMainRecordsCoreLeftOnlyThreeChunk719Pairs ∪ PeriodicMainRecordsCoreLeftOnlyThreeChunk720Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeChunk721Pairs)

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2a_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2a,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2a, Finset.mem_union] at hp
  rcases hp with ((h719 | h720) | h721)
  · exact PeriodicMainRecordsCoreLeftOnlyThreeChunk719_value_on_records p h719
  · exact PeriodicMainRecordsCoreLeftOnlyThreeChunk720_value_on_records p h720
  · exact PeriodicMainRecordsCoreLeftOnlyThreeChunk721_value_on_records p h721

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
