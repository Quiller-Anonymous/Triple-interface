import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup025
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup026

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2a : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeGroup025Pairs ∪
    PeriodicMainRecordsCoreLeftOnlyThreeGroup026Pairs

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2a_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2a,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2a, Finset.mem_union] at hp
  rcases hp with h25 | h26
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup025_value_on_records p h25
  · exact PeriodicMainRecordsCoreLeftOnlyThreeGroup026_value_on_records p h26

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
