import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionSplit
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeGroup029

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2c : Finset (ℕ × ℕ) :=
  PeriodicMainRecordsCoreLeftOnlyThreeGroup029Pairs

theorem PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2c_value_on_records :
    ∀ p ∈ PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2c,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simpa only [PeriodicMainRecordsCoreLeftOnlyThreePayloadPairsPartB2c] using
    PeriodicMainRecordsCoreLeftOnlyThreeGroup029_value_on_records p hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
