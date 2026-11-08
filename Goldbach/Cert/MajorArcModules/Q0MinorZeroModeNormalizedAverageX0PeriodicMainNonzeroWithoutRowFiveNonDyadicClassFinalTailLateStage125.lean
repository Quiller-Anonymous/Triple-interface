import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalStage124
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalLateBound286

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Checkpointed late-tail assembly stage for class groups 286..286. -/

def PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo285 ∪ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs

def PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailTotalUpTo286 : ℚ :=
  PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailTotalUpTo285 + PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Total

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo285_disjoint_PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs :
    Disjoint PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo285 PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp_previous hp_group
  have hprevious := PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo285_min_coordinate_le_1610 hp_previous
  have hgroup := PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs_min_coordinate_bounds hp_group
  omega

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286_actual_sum :
    (∑ p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailTotalUpTo286 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286, Finset.sum_union PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo285_disjoint_PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs]
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo285_actual_sum, periodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286_actual_sum]
  rfl

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286_min_coordinate_ge_1393 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286) : 1393 ≤ Nat.min p.1 p.2 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo285_min_coordinate_ge_1393 hp
  · exact (PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs_min_coordinate_bounds hp).1

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286_min_coordinate_le_1661 {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286) : Nat.min p.1 p.2 ≤ 1661 := by
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo286, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact PeriodicMainNonzeroWithoutRowFiveNonDyadicClassLateTailPairsUpTo285_min_coordinate_le_1610 hp
  · exact (PeriodicMainNonzeroWithoutRowFiveNonDyadicClassGroup286Pairs_min_coordinate_bounds hp).2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
