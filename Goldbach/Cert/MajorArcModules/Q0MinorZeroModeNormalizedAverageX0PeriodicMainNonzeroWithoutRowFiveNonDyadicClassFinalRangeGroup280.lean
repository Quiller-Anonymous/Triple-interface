import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7011
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7012
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7013
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7014
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7015
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7016
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7017
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7018
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7019
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7020
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7021
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7022
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7023
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf7024

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Structural coordinate-range assembly for non-dyadic group 280. -/

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo000_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo000) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7000Pairs_min_coordinate_le_1391 (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo000] using hp)

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo001_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo001) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo001, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo000_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7001Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo002_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo002) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo002, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo001_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7002Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo003_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo003) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo003, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo002_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7003Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo004_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo004) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo004, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo003_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7004Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo005_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo005) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo005, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo004_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7005Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo006_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo006) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo006, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo005_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7006Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo007_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo007) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo007, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo006_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7007Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo008_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo008) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo008, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo007_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7008Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo009_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo009) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo009, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo008_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7009Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo010_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo010) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo010, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo009_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7010Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo011_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo011) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo011, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo010_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7011Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo012_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo012) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo012, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo011_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7012Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo013_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo013) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo013, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo012_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7013Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo014_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo014) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo014, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo013_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7014Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo015_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo015) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo015, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo014_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7015Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo016_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo016) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo016, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo015_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7016Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo017_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo017) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo017, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo016_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7017Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo018_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo018) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo018, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo017_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7018Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo019_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo019) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo019, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo018_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7019Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo020_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo020) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo020, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo019_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7020Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo021_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo021) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo021, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo020_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7021Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo022_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo022) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo022, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo021_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7022Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo023_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo023) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo023, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo022_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7023Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo024_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo024) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo024, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo023_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass7024Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280PairsUpTo024_coordinate_bound (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs] using hp)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
