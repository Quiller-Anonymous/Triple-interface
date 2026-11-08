import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClass7108

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Constant-size coordinate certificate for non-dyadic class 7108. -/

theorem PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7108Pairs_min_coordinate_bounds {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7108Pairs) : 1393 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1493 := by
  simp [PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7108Pairs] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
