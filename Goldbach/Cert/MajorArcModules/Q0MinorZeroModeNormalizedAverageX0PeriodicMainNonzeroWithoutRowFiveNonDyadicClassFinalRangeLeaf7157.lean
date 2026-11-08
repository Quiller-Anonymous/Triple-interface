import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClass7157

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Constant-size coordinate certificate for non-dyadic class 7157. -/

theorem PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7157Pairs_min_coordinate_bounds {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7157Pairs) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  simp [PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7157Pairs] at hp
  rcases hp with rfl | rfl <;> norm_num

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
