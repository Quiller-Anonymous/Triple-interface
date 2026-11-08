import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6975
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6976
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6977
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6978
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6979
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6980
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6981
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6982
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6983
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6984
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6985
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6986
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6987
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6988
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6989
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6990
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6991
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6992
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6993
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6994
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6995
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6996
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6997
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6998
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6999

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Structural coordinate-range assembly for non-dyadic group 279. -/

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo000_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo000) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6975Pairs_min_coordinate_le_1391 (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo000] using hp)

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo001_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo001) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo001, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo000_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6976Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo002_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo002) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo002, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo001_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6977Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo003_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo003) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo003, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo002_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6978Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo004_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo004) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo004, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo003_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6979Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo005_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo005) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo005, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo004_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6980Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo006_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo006) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo006, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo005_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6981Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo007_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo007) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo007, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo006_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6982Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo008_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo008) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo008, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo007_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6983Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo009_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo009) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo009, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo008_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6984Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo010_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo010) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo010, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo009_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6985Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo011_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo011) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo011, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo010_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6986Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo012_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo012) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo012, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo011_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6987Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo013_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo013) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo013, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo012_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6988Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo014_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo014) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo014, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo013_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6989Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo015_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo015) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo015, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo014_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6990Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo016_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo016) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo016, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo015_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6991Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo017_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo017) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo017, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo016_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6992Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo018_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo018) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo018, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo017_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6993Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo019_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo019) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo019, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo018_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6994Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo020_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo020) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo020, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo019_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6995Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo021_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo021) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo021, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo020_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6996Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo022_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo022) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo022, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo021_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6997Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo023_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo023) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo023, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo022_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6998Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo024_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo024) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo024, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo023_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6999Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279PairsUpTo024_coordinate_bound (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs] using hp)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
