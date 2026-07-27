import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup027

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b1 : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeGroup027Pairs

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b1_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b1,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simpa only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2b1] using
    PeriodicMainRecordsCoreLeftOnlyThreeGroup027_value_on_records p hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
