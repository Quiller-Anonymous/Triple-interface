import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup004

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated subassembly for left-only-three zero-record payloads, groups 000-004. -/

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA0 : Finset (ℕ × ℕ) :=
  ((((PeriodicMainRecordsCoreLeftOnlyThreeGroup000Pairs ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup001Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup002Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup003Pairs) ∪ PeriodicMainRecordsCoreLeftOnlyThreeGroup004Pairs)

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA0_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA0,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartA0, Finset.mem_union] at hp
  rcases hp with ((((h0 | h1) | h2) | h3) | h4)
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup000_value_on_records p h0
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup001_value_on_records p h1
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup002_value_on_records p h2
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup003_value_on_records p h3
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup004_value_on_records p h4

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
