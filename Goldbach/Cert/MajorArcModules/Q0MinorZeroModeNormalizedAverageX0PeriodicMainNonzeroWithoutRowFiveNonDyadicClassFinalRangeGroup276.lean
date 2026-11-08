import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6900
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6901
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6902
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6903
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6904
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6905
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6906
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6907
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6908
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6909
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6910
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6911
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6912
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6913
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6914
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6915
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6916
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6917
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6918
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6919
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6920
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6921
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6922
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6923
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6924

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Structural coordinate-range assembly for non-dyadic group 276. -/

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo000_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo000) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6900Pairs_min_coordinate_le_1391 (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo000] using hp)

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo001_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo001) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo001, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo000_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6901Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo002_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo002) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo002, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo001_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6902Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo003_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo003) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo003, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo002_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6903Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo004_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo004) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo004, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo003_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6904Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo005_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo005) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo005, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo004_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6905Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo006_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo006) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo006, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo005_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6906Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo007_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo007) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo007, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo006_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6907Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo008_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo008) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo008, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo007_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6908Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo009_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo009) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo009, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo008_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6909Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo010_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo010) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo010, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo009_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6910Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo011_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo011) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo011, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo010_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6911Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo012_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo012) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo012, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo011_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6912Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo013_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo013) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo013, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo012_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6913Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo014_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo014) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo014, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo013_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6914Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo015_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo015) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo015, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo014_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6915Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo016_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo016) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo016, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo015_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6916Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo017_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo017) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo017, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo016_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6917Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo018_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo018) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo018, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo017_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6918Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo019_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo019) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo019, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo018_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6919Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo020_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo020) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo020, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo019_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6920Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo021_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo021) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo021, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo020_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6921Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo022_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo022) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo022, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo021_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6922Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo023_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo023) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo023, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo022_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6923Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo024_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo024) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo024, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo023_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6924Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276PairsUpTo024_coordinate_bound (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs] using hp)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
