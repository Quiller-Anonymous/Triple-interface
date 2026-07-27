import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk722
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk723
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeChunk724

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2b : Finset (ℕ × ℕ) :=
  ((PeriodicMainRecordsCoreLeftOnlyThreeChunk722Pairs ∪ PeriodicMainRecordsCoreLeftOnlyThreeChunk723Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeChunk724Pairs)

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2b_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2b,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b2b2b, Finset.mem_union] at hp
  rcases hp with ((h722 | h723) | h724)
  · exact PeriodicMainRecordsCoreLeftOnlyThreeChunk722_value_on_records p h722
  · exact PeriodicMainRecordsCoreLeftOnlyThreeChunk723_value_on_records p h723
  · exact PeriodicMainRecordsCoreLeftOnlyThreeChunk724_value_on_records p h724

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
