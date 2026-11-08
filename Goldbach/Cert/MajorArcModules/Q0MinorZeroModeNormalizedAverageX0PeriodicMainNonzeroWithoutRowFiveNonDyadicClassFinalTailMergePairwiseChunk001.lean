import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalStage122

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Linear coordinate-range checks for tail groups 276..278. -/

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup277Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup277Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup277Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup277Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup277Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup277Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup277Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup278Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup278Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup278Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup278Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup278Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup278Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup278Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
