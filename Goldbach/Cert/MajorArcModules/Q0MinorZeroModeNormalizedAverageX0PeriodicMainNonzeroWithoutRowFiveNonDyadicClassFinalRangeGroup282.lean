import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7050
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7051
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7052
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7053
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7054
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7055
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7056
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7057
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7058
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7059
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7060
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7061
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7062
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7063
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7064
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7065
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7066
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7067
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7068
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7069
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7070
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7071
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7072
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7073
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7074

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Structural coordinate-range assembly for non-dyadic group 282. -/

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo000_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo000) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7050Pairs_min_coordinate_le_1391 (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo000] using hp)

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo001_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo001) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo001, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo000_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7051Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo002_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo002) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo002, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo001_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7052Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo003_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo003) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo003, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo002_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7053Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo004_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo004) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo004, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo003_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7054Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo005_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo005) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo005, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo004_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7055Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo006_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo006) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo006, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo005_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7056Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo007_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo007) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo007, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo006_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7057Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo008_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo008) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo008, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo007_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7058Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo009_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo009) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo009, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo008_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7059Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo010_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo010) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo010, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo009_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7060Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo011_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo011) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo011, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo010_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7061Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo012_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo012) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo012, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo011_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7062Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo013_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo013) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo013, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo012_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7063Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo014_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo014) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo014, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo013_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7064Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo015_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo015) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo015, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo014_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7065Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo016_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo016) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo016, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo015_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7066Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo017_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo017) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo017, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo016_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7067Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo018_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo018) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo018, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo017_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7068Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo019_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo019) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo019, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo018_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7069Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo020_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo020) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo020, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo019_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7070Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo021_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo021) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo021, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo020_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7071Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo022_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo022) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo022, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo021_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7072Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo023_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo023) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo023, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo022_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7073Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo024_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo024) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo024, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo023_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7074Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282PairsUpTo024_coordinate_bound (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs] using hp)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
