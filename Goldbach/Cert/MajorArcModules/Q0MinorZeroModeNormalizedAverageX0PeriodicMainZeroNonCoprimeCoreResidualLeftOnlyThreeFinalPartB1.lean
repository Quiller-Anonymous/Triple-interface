import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup020
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup021
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup022
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup023
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup024

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated subassembly for left-only-three zero-record payloads, groups 020-024. -/

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB1 : Finset (ℕ × ℕ) :=
  ((((PeriodicMainRecordsCoreLeftOnlyThreeGroup020Pairs ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup021Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup022Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup023Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup024Pairs)

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB1_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB1,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB1, Finset.mem_union] at hp
  rcases hp with ((((h20 | h21) | h22) | h23) | h24)
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup020_value_on_records p h20
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup021_value_on_records p h21
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup022_value_on_records p h22
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup023_value_on_records p h23
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup024_value_on_records p h24

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
