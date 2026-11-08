import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7150
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7151
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7152
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7153
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7154
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7155
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7156
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7157

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Structural coordinate-range assembly for non-dyadic group 286. -/

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo000_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo000) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7150Pairs_min_coordinate_bounds (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo000] using hp)

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo001_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo001) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo001, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo000_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7151Pairs_min_coordinate_bounds hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo002_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo002) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo002, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo001_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7152Pairs_min_coordinate_bounds hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo003_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo003) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo003, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo002_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7153Pairs_min_coordinate_bounds hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo004_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo004) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo004, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo003_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7154Pairs_min_coordinate_bounds hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo005_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo005) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo005, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo004_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7155Pairs_min_coordinate_bounds hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo006_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo006) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo006, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo005_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7156Pairs_min_coordinate_bounds hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo007_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo007) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo007, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo006_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7157Pairs_min_coordinate_bounds hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs_min_coordinate_bounds {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs) : 1613 ≤ Nat.min p.1 p.2 ∧ Nat.min p.1 p.2 ≤ 1661 := by
  exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286PairsUpTo007_coordinate_bound (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs] using hp)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
