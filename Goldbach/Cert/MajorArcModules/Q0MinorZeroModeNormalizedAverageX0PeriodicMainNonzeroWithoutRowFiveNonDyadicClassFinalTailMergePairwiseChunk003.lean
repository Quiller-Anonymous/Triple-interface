import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalStage122

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Linear coordinate-range checks for tail groups 282..283. -/

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup283Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup283Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup283Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup283Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup283Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup283Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup283Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
