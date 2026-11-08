import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalStage122

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Linear coordinate-range checks for tail groups 273..275. -/

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup273Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup273Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup273Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup273Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup273Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup273Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup273Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup275Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup275Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup275Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup275Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup275Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup275Pairs.filter (fun p => Nat.min p.1 p.2 ≤ 1391) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup275Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
