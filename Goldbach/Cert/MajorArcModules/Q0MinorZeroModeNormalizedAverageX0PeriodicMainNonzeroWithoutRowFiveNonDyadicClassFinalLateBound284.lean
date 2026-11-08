import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalStage123

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Linear coordinate-range certificate for late-tail group 284. -/

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs.filter (fun p => 1393 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1493) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs_min_coordinate_bounds {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs) : 1393 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1493 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs.filter (fun p => 1393 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1493) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284_min_coordinate_ge_1393 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284) : 1393 ≤ Nat.min p.1 p.2 := by
  exact (PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs_min_coordinate_bounds (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284] using hp)).1

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284_min_coordinate_le_1493 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284) : Nat.min p.1 p.2 ≤ 1493 := by
  exact (PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup284Pairs_min_coordinate_bounds (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo284] using hp)).2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
