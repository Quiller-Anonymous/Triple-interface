import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6850
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6851
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6852
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6853
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6854
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6855
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6856
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6857
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6858
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6859
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6860
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6861
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6862
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6863
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6864
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6865
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6866
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6867
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6868
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6869
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6870
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6871
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6872
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6873
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalRangeLeaf6874

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Structural coordinate-range assembly for non-dyadic group 274. -/

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo000_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo000) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6850Pairs_min_coordinate_le_1391 (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo000] using hp)

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo001_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo001) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo001, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo000_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6851Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo002_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo002) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo002, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo001_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6852Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo003_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo003) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo003, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo002_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6853Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo004_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo004) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo004, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo003_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6854Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo005_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo005) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo005, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo004_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6855Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo006_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo006) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo006, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo005_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6856Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo007_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo007) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo007, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo006_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6857Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo008_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo008) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo008, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo007_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6858Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo009_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo009) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo009, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo008_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6859Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo010_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo010) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo010, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo009_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6860Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo011_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo011) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo011, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo010_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6861Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo012_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo012) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo012, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo011_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6862Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo013_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo013) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo013, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo012_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6863Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo014_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo014) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo014, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo013_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6864Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo015_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo015) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo015, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo014_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6865Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo016_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo016) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo016, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo015_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6866Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo017_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo017) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo017, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo016_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6867Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo018_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo018) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo018, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo017_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6868Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo019_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo019) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo019, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo018_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6869Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo020_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo020) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo020, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo019_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6870Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo021_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo021) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo021, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo020_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6871Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo022_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo022) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo022, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo021_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6872Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo023_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo023) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo023, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo022_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6873Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo024_coordinate_bound {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo024) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo024, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo023_coordinate_bound hp
  · exact PeriodicMainRecordsNonzeroWithoutRowFiveNonDyadicClass6874Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274PairsUpTo024_coordinate_bound (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs] using hp)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
