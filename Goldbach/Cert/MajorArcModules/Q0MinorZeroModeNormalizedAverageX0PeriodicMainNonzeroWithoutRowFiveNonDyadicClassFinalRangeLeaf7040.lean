import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClass7040

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Constant-size coordinate certificate for non-dyadic class 7040. -/

theorem PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7040Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7040Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  simp [PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7040Pairs] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
