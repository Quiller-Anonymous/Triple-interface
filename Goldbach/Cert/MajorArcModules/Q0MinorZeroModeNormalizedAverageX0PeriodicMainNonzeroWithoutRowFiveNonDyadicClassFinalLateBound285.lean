import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup285

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Linear coordinate-range certificate for late-tail group 285. -/

private theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup285Pairs_min_coordinate_filter :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup285Pairs.filter (fun p => 1495 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1610) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup285Pairs := by
  native_decide

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup285Pairs_min_coordinate_bounds {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup285Pairs) : 1495 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1610 := by
  have hp' : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup285Pairs.filter (fun p => 1495 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1610) := by
    rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup285Pairs_min_coordinate_filter]
    exact hp
  exact (Finset.mem_filter.mp hp').2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
