import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup011
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup012
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup013
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup014

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated subassembly for left-only-three zero-record payloads, groups 010-014. -/

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA2 : Finset (ℕ × ℕ) :=
  ((((PeriodicMainRecordsCoreLeftOnlyThreeGroup010Pairs ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup011Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup012Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup013Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup014Pairs)

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA2_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA2,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA2, Finset.mem_union] at hp
  rcases hp with ((((h10 | h11) | h12) | h13) | h14)
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup010_value_on_records p h10
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup011_value_on_records p h11
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup012_value_on_records p h12
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup013_value_on_records p h13
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup014_value_on_records p h14

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
