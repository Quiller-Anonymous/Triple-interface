import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClass7146

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Constant-size coordinate certificate for non-dyadic class 7146. -/

theorem PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7146Pairs_min_coordinate_bounds {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7146Pairs) : 1495 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1610 := by
  simp [PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7146Pairs] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
