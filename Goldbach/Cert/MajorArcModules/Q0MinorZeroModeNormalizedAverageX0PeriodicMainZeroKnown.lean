import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroResidualFinite
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroUnitTwoStructural

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach.BankParams

def PeriodicMainZeroKnownPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroUnitTwoStructuralPairs ∪ PeriodicMainZeroResidualFinitePairs

theorem PeriodicMainZeroKnown_value_on_records :
    ∀ p ∈ PeriodicMainZeroKnownPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroKnownPairs] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroUnitTwoStructural_value_on_records p hp
  · exact PeriodicMainZeroResidualFinite_value_on_records p hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
