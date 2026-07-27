import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveDyadicBridge
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup011
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMTargetGroup012

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated final target-to-LCM coverage assembly. -/

theorem PeriodicMainNonDyadicLCMTargetUpTo000_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo000)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  have hp0 : p ∈ PeriodicMainNonzeroRecordPairsGroup000 := by
    simpa [PeriodicMainNonzeroRecordPairsUpTo000] using hp
  exact PeriodicMainNonDyadicLCMTargetGroup000_subset_lcm p hp0 hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo001_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo001)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo000_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup001_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo002_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo002)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo001_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup002_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo003_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo003)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo002_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup003_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo004_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo004)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo003_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup004_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo005_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo005)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo004_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup005_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo006_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo006)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo005_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup006_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo007_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo007)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo006_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup007_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo008_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo008)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo007_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup008_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo009_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo009)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo008_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup009_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo010_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo010)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo009_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup010_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo011_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo011)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo010_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup011_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonDyadicLCMTargetUpTo012_subset_lcm
    (p : ℕ × ℕ)
    (hp : p ∈ PeriodicMainNonzeroRecordPairsUpTo012)
    (hnotrow : p ∉ PeriodicMainNonzeroRecordPairsRowFive)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonDyadicLCMPairs := by
  rw [PeriodicMainNonzeroRecordPairsUpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMTargetUpTo011_subset_lcm p hp hnotrow hnotdyadic
  · exact PeriodicMainNonDyadicLCMTargetGroup012_subset_lcm p hp hnotrow hnotdyadic

theorem PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic_subset_lcm :
    PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic ⊆ PeriodicMainNonDyadicLCMPairs := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic] at hp
  rcases Finset.mem_filter.mp hp with ⟨hp_without, hnotdyadic⟩
  rw [PeriodicMainNonzeroRecordPairsWithoutRowFive] at hp_without
  rcases Finset.mem_sdiff.mp hp_without with ⟨hp_nonzero, hnotrow⟩
  have hp_nonzero' : p ∈ PeriodicMainNonzeroRecordPairsUpTo012 := by
    simpa [PeriodicMainNonzeroRecordPairs] using hp_nonzero
  exact PeriodicMainNonDyadicLCMTargetUpTo012_subset_lcm p hp_nonzero' hnotrow hnotdyadic

/- nonzero target group count=13, chunk count=307 -/

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
