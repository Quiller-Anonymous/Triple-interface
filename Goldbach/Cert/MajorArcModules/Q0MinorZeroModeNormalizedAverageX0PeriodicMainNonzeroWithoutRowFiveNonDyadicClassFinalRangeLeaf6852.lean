import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClass6852

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Constant-size coordinate certificate for non-dyadic class 6852. -/

theorem PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6852Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6852Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  simp [PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6852Pairs] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
