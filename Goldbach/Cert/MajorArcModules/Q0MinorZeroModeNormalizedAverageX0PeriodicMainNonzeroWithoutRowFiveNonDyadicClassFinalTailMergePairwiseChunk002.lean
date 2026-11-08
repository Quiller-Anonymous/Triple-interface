import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalStage122

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Linear coordinate-range checks for tail groups 279..281. -/

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup281Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup281Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup281Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup281Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup281Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup281Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup281Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
