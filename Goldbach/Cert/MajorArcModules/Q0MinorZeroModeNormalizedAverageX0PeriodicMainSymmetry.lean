import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem evenRamanujanBlockCountRat_comm
    (X q q' : ℕ) :
    evenRamanujanBlockCountRat q q' =
      evenRamanujanBlockCountRat q' q := by
  have h := evenRamanujanBlockCount_comm X q q'
  rw [evenRamanujanBlockCount_eq_ratCast,
    evenRamanujanBlockCount_eq_ratCast] at h
  exact Rat.cast_injective (α := ℝ) h

theorem rawEvenRamanujanGcdClassBlockPeriodicCountRat_comm
    (X q q' q0 g0 : ℕ) :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q0 g0 =
      rawEvenRamanujanGcdClassBlockPeriodicCountRat X q' q q0 g0 := by
  have h := rawEvenRamanujanGcdClassBlockPeriodicCount_comm X q q' q0 g0
  rw [rawEvenRamanujanGcdClassBlockPeriodicCount_eq_ratCast,
    rawEvenRamanujanGcdClassBlockPeriodicCount_eq_ratCast] at h
  exact Rat.cast_injective (α := ℝ) h

theorem rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_comm
    (X q q' g h : ℕ) :
    rawEvenRamanujanGcdClassPairBlockPeriodicCountRat X q q' g h =
      rawEvenRamanujanGcdClassPairBlockPeriodicCountRat X q' q h g := by
  have hcomm := rawEvenRamanujanGcdClassPairBlockPeriodicCount_comm X q q' g h
  rw [rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_ratCast,
    rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_ratCast] at hcomm
  exact Rat.cast_injective (α := ℝ) hcomm

theorem ramanujanGcdClassJointCompatibility_comm
    (q q' g h : ℕ) :
    ramanujanGcdClassJointCompatibility q q' g h ↔
      ramanujanGcdClassJointCompatibility q' q h g := by
  unfold ramanujanGcdClassJointCompatibility
  constructor <;> intro hcompat <;>
    simpa [Nat.lcm_comm, and_comm] using hcompat

theorem rawEvenRamanujanGcdClassPairBlockResolvedCountRat_comm
    (X q q' g h : ℕ) :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q q' g h =
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q' q h g := by
  unfold rawEvenRamanujanGcdClassPairBlockResolvedCountRat
  by_cases hcompat : ramanujanGcdClassJointCompatibility q q' g h
  · have hcompat' :
        ramanujanGcdClassJointCompatibility q' q h g :=
      (ramanujanGcdClassJointCompatibility_comm q q' g h).mp hcompat
    simp [hcompat, hcompat', rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_comm]
  · have hcompat' :
        ¬ ramanujanGcdClassJointCompatibility q' q h g := by
      intro hswap
      exact hcompat ((ramanujanGcdClassJointCompatibility_comm q q' g h).mpr hswap)
    simp [hcompat, hcompat']

theorem centeredRamanujanPairPeriodicMainTermRat_comm
    (X q q' : ℕ) :
    centeredRamanujanPairPeriodicMainTermRat X q q' =
      centeredRamanujanPairPeriodicMainTermRat X q' q := by
  unfold centeredRamanujanPairPeriodicMainTermRat
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro h hh
  refine Finset.sum_congr rfl ?_
  intro g hg
  rw [centeredRamanujanPairBlockPeriod_comm]
  rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_comm]
  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_comm X q q' q g]
  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_comm X q q' q' h]
  rw [evenRamanujanBlockCountRat_comm X]
  ring

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_swap
    (X q q' : ℕ) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X (q, q') =
      surrogatePeriodicMainActiveOrderedPairSummandRat X (q', q) := by
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat
  by_cases hdiag : q = q'
  · subst q'
    simp
  · have hdiag' : q' ≠ q := by
      exact Ne.symm hdiag
    simp [hdiag, hdiag']
    rw [centeredRamanujanPairPeriodicMainTermRat_comm X q q']
    ring

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
