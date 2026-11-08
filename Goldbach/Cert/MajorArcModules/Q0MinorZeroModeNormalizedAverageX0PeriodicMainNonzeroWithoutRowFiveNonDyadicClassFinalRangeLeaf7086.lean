import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClass7086

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Constant-size coordinate certificate for non-dyadic class 7086. -/

theorem PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7086Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7086Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  simp [PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7086Pairs] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
