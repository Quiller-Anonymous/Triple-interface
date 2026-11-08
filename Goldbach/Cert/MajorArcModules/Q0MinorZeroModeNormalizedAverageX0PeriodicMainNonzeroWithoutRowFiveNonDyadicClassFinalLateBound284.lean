import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalStage123
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeGroup284

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Late-tail coordinate interface for group 284. -/

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284_min_coordinate_ge_1393 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284) : 1393 ≤ Nat.min p.1 p.2 := by
  exact (PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs_min_coordinate_bounds (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284] using hp)).1

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284_min_coordinate_le_1493 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284) : Nat.min p.1 p.2 ≤ 1493 := by
  exact (PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs_min_coordinate_bounds (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284] using hp)).2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
