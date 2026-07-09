import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidual
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeStructuralProbe

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def bothThreeOddCore (q : ℕ) : ℕ :=
  if Goldbach.Windows.IsEven (q / 3) then
    (q / 3) / 2
  else
    q / 3

private theorem forall_mem_of_bad_filter_card_zero
    {α : Type*} [DecidableEq α] {s : Finset α} {P : α → Prop}
    [DecidablePred P]
    (hcard : (s.filter (fun x => ! decide (P x))).card = 0) :
    ∀ x ∈ s, P x := by
  intro x hx
  by_contra hPx
  have hxBad : x ∈ s.filter (fun x => ! decide (P x)) := by
    exact Finset.mem_filter.mpr ⟨hx, by simp [hPx]⟩
  have hEmpty : s.filter (fun x => ! decide (P x)) = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hEmpty] at hxBad
  simp at hxBad

def bothThreeOddCoreStructuralGood (p : ℕ × ℕ) : Prop :=
  ¬ Goldbach.Windows.IsEven (bothThreeOddCore p.1)
    ∧ ¬ Goldbach.Windows.IsEven (bothThreeOddCore p.2)
    ∧ ¬ 3 ∣ bothThreeOddCore p.1
    ∧ ¬ 3 ∣ bothThreeOddCore p.2
    ∧ bothThreeOddCore p.1 ≠ bothThreeOddCore p.2
    ∧ (p.1 = 3 * bothThreeOddCore p.1 ∨ p.1 = 6 * bothThreeOddCore p.1)
    ∧ (p.2 = 3 * bothThreeOddCore p.2 ∨ p.2 = 6 * bothThreeOddCore p.2)

instance instDecidableBothThreeOddCoreStructuralGood
    (p : ℕ × ℕ) : Decidable (bothThreeOddCoreStructuralGood p) := by
  unfold bothThreeOddCoreStructuralGood
  infer_instance

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeStructuralBadPairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs.filter
    (fun p => ! decide (bothThreeOddCoreStructuralGood p))

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeStructuralBadPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeStructuralBadPairs.card = 0 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_structural_good :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      bothThreeOddCoreStructuralGood p := by
  exact forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs)
    (P := bothThreeOddCoreStructuralGood)
    (by
      simpa [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeStructuralBadPairs]
        using PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeStructuralBadPairs_card)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_odd :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      ¬ Goldbach.Windows.IsEven (bothThreeOddCore p.1) := by
  intro p hp
  exact (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_structural_good p hp).1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_odd :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      ¬ Goldbach.Windows.IsEven (bothThreeOddCore p.2) := by
  intro p hp
  exact (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_structural_good p hp).2.1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_not_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      ¬ 3 ∣ bothThreeOddCore p.1 := by
  intro p hp
  exact (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_structural_good p hp).2.2.1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_not_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      ¬ 3 ∣ bothThreeOddCore p.2 := by
  intro p hp
  exact (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_structural_good p hp).2.2.2.1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_odd_cores_ne :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      bothThreeOddCore p.1 ≠ bothThreeOddCore p.2 := by
  intro p hp
  exact (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_structural_good p hp).2.2.2.2.1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_eq_three_or_six_mul_core :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      p.1 = 3 * bothThreeOddCore p.1 ∨ p.1 = 6 * bothThreeOddCore p.1 := by
  intro p hp
  exact (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_structural_good p hp).2.2.2.2.2.1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_eq_three_or_six_mul_core :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      p.2 = 3 * bothThreeOddCore p.2 ∨ p.2 = 6 * bothThreeOddCore p.2 := by
  intro p hp
  exact (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_structural_good p hp).2.2.2.2.2.2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
