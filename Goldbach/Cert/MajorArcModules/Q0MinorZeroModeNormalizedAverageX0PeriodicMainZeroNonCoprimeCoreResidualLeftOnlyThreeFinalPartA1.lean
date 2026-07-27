import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup009

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated subassembly for left-only-three zero-record payloads, groups 005-009. -/

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA1 : Finset (ℕ × ℕ) :=
  ((((PeriodicMainRecordsCoreLeftOnlyThreeGroup005Pairs ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup006Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup007Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup008Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup009Pairs)

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA1_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA1,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA1, Finset.mem_union] at hp
  rcases hp with ((((h5 | h6) | h7) | h8) | h9)
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup005_value_on_records p h5
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup006_value_on_records p h6
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup007_value_on_records p h7
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup008_value_on_records p h8
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup009_value_on_records p h9

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
