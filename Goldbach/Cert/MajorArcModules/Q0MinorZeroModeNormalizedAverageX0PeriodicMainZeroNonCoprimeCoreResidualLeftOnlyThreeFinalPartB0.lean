import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup015
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup016
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup017
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup018
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup019

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated subassembly for left-only-three zero-record payloads, groups 015-019. -/

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB0 : Finset (ℕ × ℕ) :=
  ((((PeriodicMainRecordsCoreLeftOnlyThreeGroup015Pairs ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup016Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup017Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup018Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup019Pairs)

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB0_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB0,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB0, Finset.mem_union] at hp
  rcases hp with ((((h15 | h16) | h17) | h18) | h19)
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup015_value_on_records p h15
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup016_value_on_records p h16
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup017_value_on_records p h17
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup018_value_on_records p h18
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup019_value_on_records p h19

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
