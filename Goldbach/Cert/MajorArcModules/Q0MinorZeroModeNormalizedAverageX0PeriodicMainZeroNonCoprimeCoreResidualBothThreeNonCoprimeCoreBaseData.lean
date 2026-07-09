import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeAverageValues

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Shared data surface for the non-coprime-core `bothThree` proof.

The expensive finite raw check is split into left-core ranges in separate chunk
modules.  This file keeps only the common predicates and cheap finite coverage
facts.
-/

theorem nonCoprimeCore_forall_mem_of_bad_filter_card_zero
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

def bothThreeNonCoprimeCoreRawCorePairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs.image
    (fun p => (bothThreeOddCore p.1, bothThreeOddCore p.2))

def bothThreeNonCoprimeCoreRawCorePairGood (p : ℕ × ℕ) : Prop :=
  rawEvenRamanujanPairBlockSumRat X0 p.1 p.2 = 0

instance instDecidableBothThreeNonCoprimeCoreRawCorePairGood
    (p : ℕ × ℕ) : Decidable (bothThreeNonCoprimeCoreRawCorePairGood p) := by
  unfold bothThreeNonCoprimeCoreRawCorePairGood
  infer_instance

def bothThreeNonCoprimeCoreRawCoreBadPairsInLeftRange
    (lo hi : ℕ) : Finset (ℕ × ℕ) :=
  bothThreeNonCoprimeCoreRawCorePairs.filter
    (fun p =>
      if lo ≤ p.1 then
        if p.1 < hi then
          ! decide (bothThreeNonCoprimeCoreRawCorePairGood p)
        else
          false
      else
        false)

theorem bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
    {lo hi : ℕ}
    (hcard :
      (bothThreeNonCoprimeCoreRawCoreBadPairsInLeftRange lo hi).card = 0)
    {ab : ℕ × ℕ}
    (hab : ab ∈ bothThreeNonCoprimeCoreRawCorePairs)
    (hlo : lo ≤ ab.1) (hhi : ab.1 < hi) :
    bothThreeNonCoprimeCoreRawCorePairGood ab := by
  by_contra hgood
  have hbad : ab ∈ bothThreeNonCoprimeCoreRawCoreBadPairsInLeftRange lo hi := by
    exact Finset.mem_filter.mpr ⟨hab, by simp [hlo, hhi, hgood]⟩
  have hempty : bothThreeNonCoprimeCoreRawCoreBadPairsInLeftRange lo hi = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hempty] at hbad
  simp at hbad

theorem bothThreeNonCoprimeCoreRawCorePairs_card :
    bothThreeNonCoprimeCoreRawCorePairs.card = 346 := by
  native_decide

def bothThreeNonCoprimeCoreRawCoreOutOfRangePairs : Finset (ℕ × ℕ) :=
  bothThreeNonCoprimeCoreRawCorePairs.filter (fun p => ! decide (p.1 < 2000))

theorem bothThreeNonCoprimeCoreRawCoreOutOfRangePairs_card :
    bothThreeNonCoprimeCoreRawCoreOutOfRangePairs.card = 0 := by
  native_decide

theorem bothThreeNonCoprimeCoreRawCore_left_lt_2000_of_mem
    {ab : ℕ × ℕ} (hab : ab ∈ bothThreeNonCoprimeCoreRawCorePairs) :
    ab.1 < 2000 := by
  exact nonCoprimeCore_forall_mem_of_bad_filter_card_zero
    (s := bothThreeNonCoprimeCoreRawCorePairs)
    (P := fun p : ℕ × ℕ => p.1 < 2000)
    (by
      simpa [bothThreeNonCoprimeCoreRawCoreOutOfRangePairs]
        using bothThreeNonCoprimeCoreRawCoreOutOfRangePairs_card)
    ab hab

def bothThreeNonCoprimeCoreAverageZeroCoreGood (p : ℕ × ℕ) : Prop :=
  bothThreeOddCore p.1 ∈ bothThreeCoprimeCoreAverageZeroCores
    ∨ bothThreeOddCore p.2 ∈ bothThreeCoprimeCoreAverageZeroCores

instance instDecidableBothThreeNonCoprimeCoreAverageZeroCoreGood
    (p : ℕ × ℕ) : Decidable (bothThreeNonCoprimeCoreAverageZeroCoreGood p) := by
  unfold bothThreeNonCoprimeCoreAverageZeroCoreGood
  infer_instance

def bothThreeNonCoprimeCoreAverageZeroCoreBadPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs.filter
    (fun p => ! decide (bothThreeNonCoprimeCoreAverageZeroCoreGood p))

theorem bothThreeNonCoprimeCoreAverageZeroCoreBadPairs_card :
    bothThreeNonCoprimeCoreAverageZeroCoreBadPairs.card = 0 := by
  native_decide

theorem bothThreeNonCoprimeCoreAverageZeroCoreGood_of_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs) :
    bothThreeNonCoprimeCoreAverageZeroCoreGood p := by
  exact nonCoprimeCore_forall_mem_of_bad_filter_card_zero
    (s := PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs)
    (P := bothThreeNonCoprimeCoreAverageZeroCoreGood)
    (by
      simpa [bothThreeNonCoprimeCoreAverageZeroCoreBadPairs]
        using bothThreeNonCoprimeCoreAverageZeroCoreBadPairs_card)
    p hp

theorem bothThreeNonCoprimeCoreAverageGood_of_zeroCoreGood
    {p : ℕ × ℕ}
    (hzero : bothThreeNonCoprimeCoreAverageZeroCoreGood p)
    (hvalue :
      ∀ a ∈ bothThreeCoprimeCoreAverageZeroCores,
        bothThreeCoprimeCoreAverageZeroCoreValueGood a) :
    bothThreeCoprimeCoreAverageGood p := by
  unfold bothThreeNonCoprimeCoreAverageZeroCoreGood
    bothThreeCoprimeCoreAverageGood at *
  rcases hzero with hleft | hright
  · exact Or.inl (hvalue (bothThreeOddCore p.1) hleft)
  · exact Or.inr (hvalue (bothThreeOddCore p.2) hright)

theorem bothThreeNonCoprimeCoreAverageGood_of_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs)
    (hvalue :
      ∀ a ∈ bothThreeCoprimeCoreAverageZeroCores,
        bothThreeCoprimeCoreAverageZeroCoreValueGood a) :
    bothThreeCoprimeCoreAverageGood p :=
  bothThreeNonCoprimeCoreAverageGood_of_zeroCoreGood
    (bothThreeNonCoprimeCoreAverageZeroCoreGood_of_mem hp) hvalue

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
