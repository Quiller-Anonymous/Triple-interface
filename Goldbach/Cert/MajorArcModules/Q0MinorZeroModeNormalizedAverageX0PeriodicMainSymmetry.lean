import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem ramanujanGcdClassJointCompatibility_comm
    {q q' g h : ℕ} :
    ramanujanGcdClassJointCompatibility q q' g h ↔
      ramanujanGcdClassJointCompatibility q' q h g := by
  unfold ramanujanGcdClassJointCompatibility
  constructor
  · intro hcompat
    constructor
    · simpa [Nat.lcm_comm] using hcompat.2
    · simpa [Nat.lcm_comm] using hcompat.1
  · intro hcompat
    constructor
    · simpa [Nat.lcm_comm] using hcompat.2
    · simpa [Nat.lcm_comm] using hcompat.1

theorem rawEvenRamanujanGcdClassPairBlockResolvedCount_comm
    (X q q' g h : ℕ) :
    rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h =
      rawEvenRamanujanGcdClassPairBlockResolvedCount X q' q h g := by
  unfold rawEvenRamanujanGcdClassPairBlockResolvedCount
  by_cases hcompat : ramanujanGcdClassJointCompatibility q q' g h
  · have hcompat' :
        ramanujanGcdClassJointCompatibility q' q h g :=
      ramanujanGcdClassJointCompatibility_comm.mp hcompat
    simp [hcompat, hcompat', rawEvenRamanujanGcdClassPairBlockPeriodicCount_comm]
  · have hcompat' :
        ¬ ramanujanGcdClassJointCompatibility q' q h g := by
      intro h'
      exact hcompat (ramanujanGcdClassJointCompatibility_comm.mpr h')
    simp [hcompat, hcompat']

theorem rawEvenRamanujanGcdClassPairBlockResolvedCountRat_comm
    (X q q' g h : ℕ) :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q q' g h =
      rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q' q h g := by
  apply Rat.cast_injective (α := ℝ)
  rw [← rawEvenRamanujanGcdClassPairBlockResolvedCount_eq_ratCast,
    ← rawEvenRamanujanGcdClassPairBlockResolvedCount_eq_ratCast]
  exact rawEvenRamanujanGcdClassPairBlockResolvedCount_comm X q q' g h

theorem rawEvenRamanujanGcdClassBlockPeriodicCountRat_comm
    (X q q' q0 g0 : ℕ) :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q0 g0 =
      rawEvenRamanujanGcdClassBlockPeriodicCountRat X q' q q0 g0 := by
  apply Rat.cast_injective (α := ℝ)
  rw [← rawEvenRamanujanGcdClassBlockPeriodicCount_eq_ratCast,
    ← rawEvenRamanujanGcdClassBlockPeriodicCount_eq_ratCast]
  exact rawEvenRamanujanGcdClassBlockPeriodicCount_comm X q q' q0 g0

theorem evenRamanujanBlockCountRat_comm
    (q q' : ℕ) :
    evenRamanujanBlockCountRat q q' = evenRamanujanBlockCountRat q' q := by
  apply Rat.cast_injective (α := ℝ)
  rw [← evenRamanujanBlockCount_eq_ratCast,
    ← evenRamanujanBlockCount_eq_ratCast]
  exact evenRamanujanBlockCount_comm X0 q q'

theorem centeredRamanujanPairPeriodicMainTermRat_comm
    (X q q' : ℕ) :
    centeredRamanujanPairPeriodicMainTermRat X q q' =
      centeredRamanujanPairPeriodicMainTermRat X q' q := by
  unfold centeredRamanujanPairPeriodicMainTermRat
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  refine Finset.sum_congr rfl ?_
  intro g _hg
  rw [centeredRamanujanPairBlockPeriod_comm]
  rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_comm]
  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_comm X q q' q g]
  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_comm X q q' q' h]
  rw [evenRamanujanBlockCountRat_comm]
  ring

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_comm
    (X q q' : ℕ) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X (q, q') =
      surrogatePeriodicMainActiveOrderedPairSummandRat X (q', q) := by
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat
  by_cases hdiag : q = q'
  · subst q'
    simp
  · have hdiag' : q' ≠ q := fun h => hdiag h.symm
    simp [hdiag, hdiag', centeredRamanujanPairPeriodicMainTermRat_comm, mul_comm]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
