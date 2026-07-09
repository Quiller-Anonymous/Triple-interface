import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeRawCore

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Average-zero surface for the coprime-core part of `bothThree`.

The raw pair block is now structural.  The remaining centered-term condition for
coprime odd cores is that at least one of the two `3 * core` one-variable
window averages is zero.  This module packages that as a small finite core
lookup rather than a record-by-record exact fallback.
-/

private theorem averageCore_forall_mem_of_bad_filter_card_zero
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

def bothThreeCoprimeCoreAverageZeroCores : Finset ℕ :=
  [7, 17, 37, 43, 67, 79, 83, 89, 103, 113, 119, 127, 139, 151, 211, 241,
    271, 277, 281, 283, 331].toFinset

def bothThreeCoprimeCoreAverageZeroCoreValueGood (a : ℕ) : Prop :=
  ramanujanWindowAverageByGcdRat X0 (3 * a) = 0

structure BothThreeCoprimeCoreAverageValueCertificateAtX0 : Prop where
  value_on_zero_cores :
    ∀ a ∈ bothThreeCoprimeCoreAverageZeroCores,
      bothThreeCoprimeCoreAverageZeroCoreValueGood a

def bothThreeCoprimeCoreAverageZeroCoreGood (p : ℕ × ℕ) : Prop :=
  bothThreeOddCore p.1 ∈ bothThreeCoprimeCoreAverageZeroCores
    ∨ bothThreeOddCore p.2 ∈ bothThreeCoprimeCoreAverageZeroCores

instance instDecidableBothThreeCoprimeCoreAverageZeroCoreGood
    (p : ℕ × ℕ) : Decidable (bothThreeCoprimeCoreAverageZeroCoreGood p) := by
  unfold bothThreeCoprimeCoreAverageZeroCoreGood
  infer_instance

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreAverageZeroCoreBadPairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs.filter
    (fun p => ! decide (bothThreeCoprimeCoreAverageZeroCoreGood p))

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreAverageZeroCoreBadPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreAverageZeroCoreBadPairs.card = 0 := by
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreGood_of_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    bothThreeCoprimeCoreAverageZeroCoreGood p := by
  exact averageCore_forall_mem_of_bad_filter_card_zero
    (s := PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (P := bothThreeCoprimeCoreAverageZeroCoreGood)
    (by
      simpa [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreAverageZeroCoreBadPairs]
        using PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreAverageZeroCoreBadPairs_card)
    p hp

theorem bothThreeCoprimeCoreAverageGood_of_zeroCoreGood
    {p : ℕ × ℕ}
    (hzero : bothThreeCoprimeCoreAverageZeroCoreGood p)
    (hvalue :
      ∀ a ∈ bothThreeCoprimeCoreAverageZeroCores,
        bothThreeCoprimeCoreAverageZeroCoreValueGood a) :
    bothThreeCoprimeCoreAverageGood p := by
  unfold bothThreeCoprimeCoreAverageGood bothThreeCoprimeCoreAverageZeroCoreGood at *
  rcases hzero with hleft | hright
  · exact Or.inl (hvalue (bothThreeOddCore p.1) hleft)
  · exact Or.inr (hvalue (bothThreeOddCore p.2) hright)

theorem bothThreeCoprimeCoreAverageGood_of_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hvalue :
      ∀ a ∈ bothThreeCoprimeCoreAverageZeroCores,
        bothThreeCoprimeCoreAverageZeroCoreValueGood a) :
    bothThreeCoprimeCoreAverageGood p :=
  bothThreeCoprimeCoreAverageGood_of_zeroCoreGood
    (bothThreeCoprimeCoreAverageZeroCoreGood_of_mem hp) hvalue

theorem bothThreeCoprimeCoreAverageGood_of_mem_of_averageValueCert
    (cert : BothThreeCoprimeCoreAverageValueCertificateAtX0)
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    bothThreeCoprimeCoreAverageGood p :=
  bothThreeCoprimeCoreAverageGood_of_mem hp cert.value_on_zero_cores

theorem bothThreeBaseFullBlockZeroAtX0_of_coprimeCore_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hvalue :
      ∀ a ∈ bothThreeCoprimeCoreAverageZeroCores,
        bothThreeCoprimeCoreAverageZeroCoreValueGood a) :
    bothThreeBaseFullBlockZeroAtX0 p :=
  bothThreeBaseFullBlockZeroAtX0_of_coprimeCoreRawGood_of_averageGood hp
    (bothThreeCoprimeCoreRawGood_of_mem hp)
    (bothThreeCoprimeCoreAverageGood_of_mem hp hvalue)

theorem bothThreeBaseFullBlockZeroAtX0_of_coprimeCore_mem_of_averageValueCert
    (cert : BothThreeCoprimeCoreAverageValueCertificateAtX0)
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    bothThreeBaseFullBlockZeroAtX0 p :=
  bothThreeBaseFullBlockZeroAtX0_of_coprimeCore_mem hp cert.value_on_zero_cores

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
