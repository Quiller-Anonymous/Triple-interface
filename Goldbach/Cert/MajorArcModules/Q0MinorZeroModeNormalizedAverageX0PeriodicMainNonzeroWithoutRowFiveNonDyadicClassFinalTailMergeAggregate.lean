import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalTailMergePairwiseChunk000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalTailMergePairwiseChunk001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalTailMergePairwiseChunk002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalTailMergePairwiseChunk003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalTailLateStage125

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Structural disjointness assembly for tail groups 273..283 against the late tail. -/

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo273_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo273) : Nat.min p.1 p.2 ≤ 1391 := by
  exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup273Pairs_min_coordinate_le_1391 (by simpa [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo273] using hp)

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo274_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo274) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo274, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo273_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup274Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo275_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo275) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo275, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo274_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup275Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo276_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo276) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo276, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo275_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup276Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo277_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo277) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo277, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo276_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup277Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo278_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo278) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo278, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo277_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup278Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo279_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo279) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo279, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo278_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup279Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo280_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo280) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo280, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo279_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup280Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo281_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo281) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo281, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo280_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup281Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo282_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo282) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo282, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo281_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup282Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo283_min_coordinate_le_1391 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo283) : Nat.min p.1 p.2 ≤ 1391 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo283, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo282_min_coordinate_le_1391 hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup283Pairs_min_coordinate_le_1391 hp

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo283_disjoint_PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286 :
    Disjoint PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo283 PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286 := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp_tail hp_late
  have htail := PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTailPairsUpTo283_min_coordinate_le_1391 hp_tail
  have hlate := PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286_min_coordinate_ge_1393 hp_late
  omega

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
