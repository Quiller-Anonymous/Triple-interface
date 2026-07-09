import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeCoprimeBase

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Reduced certificate surface for the coprime-core part of `bothThree`.

The structural common-three proof in `BothThreeCoprimeBase` already proves that
the two one-variable raw block sums vanish for every coprime-core record.  This
module leaves only the residual facts that have not yet been structuralized:

* the core raw pair block sum is zero;
* at least one base-window average is zero.
-/

def bothThreeCoprimeCoreReducedGood (p : ℕ × ℕ) : Prop :=
  let a := bothThreeOddCore p.1
  let b := bothThreeOddCore p.2
  rawEvenRamanujanPairBlockSumRat X0 a b = 0
    ∧ (ramanujanWindowAverageByGcdRat X0 (3 * a) = 0
        ∨ ramanujanWindowAverageByGcdRat X0 (3 * b) = 0)

instance instDecidableBothThreeCoprimeCoreReducedGood
    (p : ℕ × ℕ) : Decidable (bothThreeCoprimeCoreReducedGood p) := by
  unfold bothThreeCoprimeCoreReducedGood
  infer_instance

def bothThreeCoprimeCoreRawGood (p : ℕ × ℕ) : Prop :=
  let a := bothThreeOddCore p.1
  let b := bothThreeOddCore p.2
  rawEvenRamanujanPairBlockSumRat X0 a b = 0

instance instDecidableBothThreeCoprimeCoreRawGood
    (p : ℕ × ℕ) : Decidable (bothThreeCoprimeCoreRawGood p) := by
  unfold bothThreeCoprimeCoreRawGood
  infer_instance

def bothThreeCoprimeCoreAverageGood (p : ℕ × ℕ) : Prop :=
  let a := bothThreeOddCore p.1
  let b := bothThreeOddCore p.2
  ramanujanWindowAverageByGcdRat X0 (3 * a) = 0
    ∨ ramanujanWindowAverageByGcdRat X0 (3 * b) = 0

instance instDecidableBothThreeCoprimeCoreAverageGood
    (p : ℕ × ℕ) : Decidable (bothThreeCoprimeCoreAverageGood p) := by
  unfold bothThreeCoprimeCoreAverageGood
  infer_instance

theorem bothThreeCoprimeCoreReducedGood_of_rawGood_of_averageGood
    {p : ℕ × ℕ}
    (hraw : bothThreeCoprimeCoreRawGood p)
    (havg : bothThreeCoprimeCoreAverageGood p) :
    bothThreeCoprimeCoreReducedGood p := by
  unfold bothThreeCoprimeCoreReducedGood bothThreeCoprimeCoreRawGood
    bothThreeCoprimeCoreAverageGood at *
  exact ⟨hraw, havg⟩

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreRawBadPairsInLeftRange
    (lo hi : ℕ) :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs.filter
    (fun p =>
      if lo ≤ p.1 then
        if p.1 < hi then
          ! decide (bothThreeCoprimeCoreRawGood p)
        else
          false
      else
        false)

theorem bothThreeCoprimeCoreRawGood_of_badPairsInLeftRange_card_zero
    {lo hi : ℕ}
    (hcard :
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreRawBadPairsInLeftRange
        lo hi).card = 0)
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hlo : lo ≤ p.1) (hhi : p.1 < hi) :
    bothThreeCoprimeCoreRawGood p := by
  by_contra hgood
  have hbad :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreRawBadPairsInLeftRange
        lo hi := by
    exact Finset.mem_filter.mpr ⟨hp, by simp [hlo, hhi, hgood]⟩
  have hempty :
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreRawBadPairsInLeftRange
        lo hi
        = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hempty] at hbad
  simp at hbad

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreAverageBadPairsInLeftRange
    (lo hi : ℕ) :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs.filter
    (fun p =>
      if lo ≤ p.1 then
        if p.1 < hi then
          ! decide (bothThreeCoprimeCoreAverageGood p)
        else
          false
      else
        false)

theorem bothThreeCoprimeCoreAverageGood_of_badPairsInLeftRange_card_zero
    {lo hi : ℕ}
    (hcard :
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreAverageBadPairsInLeftRange
        lo hi).card = 0)
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hlo : lo ≤ p.1) (hhi : p.1 < hi) :
    bothThreeCoprimeCoreAverageGood p := by
  by_contra hgood
  have hbad :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreAverageBadPairsInLeftRange
        lo hi := by
    exact Finset.mem_filter.mpr ⟨hp, by simp [hlo, hhi, hgood]⟩
  have hempty :
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreAverageBadPairsInLeftRange
        lo hi
        = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hempty] at hbad
  simp at hbad

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreReducedBadPairsInLeftRange
    (lo hi : ℕ) : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs.filter
    (fun p =>
      if lo ≤ p.1 then
        if p.1 < hi then
          ! decide (bothThreeCoprimeCoreReducedGood p)
        else
          false
      else
        false)

theorem bothThreeCoprimeCoreReducedGood_of_badPairsInLeftRange_card_zero
    {lo hi : ℕ}
    (hcard :
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreReducedBadPairsInLeftRange
        lo hi).card = 0)
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hlo : lo ≤ p.1) (hhi : p.1 < hi) :
    bothThreeCoprimeCoreReducedGood p := by
  by_contra hgood
  have hbad :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreReducedBadPairsInLeftRange
        lo hi := by
    exact Finset.mem_filter.mpr ⟨hp, by simp [hlo, hhi, hgood]⟩
  have hempty :
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreReducedBadPairsInLeftRange
        lo hi = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hempty] at hbad
  simp at hbad

theorem bothThreeBaseFullBlockZeroAtX0_of_coprimeCoreReducedGood
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hgood : bothThreeCoprimeCoreReducedGood p) :
    bothThreeBaseFullBlockZeroAtX0 p := by
  let a := bothThreeOddCore p.1
  let b := bothThreeOddCore p.2
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree
      p hp
  have hgood' :
      rawEvenRamanujanPairBlockSumRat X0 a b = 0
        ∧ (ramanujanWindowAverageByGcdRat X0 (3 * a) = 0
            ∨ ramanujanWindowAverageByGcdRat X0 (3 * b) = 0) := by
    simpa [bothThreeCoprimeCoreReducedGood, a, b] using hgood
  rcases hgood' with ⟨hcoreRat, havgRat⟩
  have hcoreReal : rawEvenRamanujanPairBlockSum X0 a b = 0 := by
    rw [rawEvenRamanujanPairBlockSum_eq_ratCast]
    rw [hcoreRat]
    norm_num
  have hapos : 1 ≤ 3 * a := by
    have ha0 : 0 < a := by
      simpa [a] using
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_pos
          hpBoth
    omega
  have hbpos : 1 ≤ 3 * b := by
    have hb0 : 0 < b := by
      simpa [b] using
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_pos
          hpBoth
    omega
  have havgReal :
      ramanujanWindowAverage X0 (3 * a) = 0
        ∨ ramanujanWindowAverage X0 (3 * b) = 0 := by
    rcases havgRat with havgLeft | havgRight
    · left
      rw [ramanujanWindowAverage_eq_ratCast_ramanujanWindowAverageByGcdRat
        (X := X0) (q := 3 * a) hapos]
      rw [havgLeft]
      norm_num
    · right
      rw [ramanujanWindowAverage_eq_ratCast_ramanujanWindowAverageByGcdRat
        (X := X0) (q := 3 * b) hbpos]
      rw [havgRight]
      norm_num
  exact
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_baseFullBlockZero_of_corePairRawBlockSum_zero
      (p := p) hp (by simpa [a, b] using hcoreReal)
      (by simpa [a, b] using havgReal)

theorem bothThreeBaseFullBlockZeroAtX0_of_coprimeCoreRawGood_of_averageGood
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hraw : bothThreeCoprimeCoreRawGood p)
    (havg : bothThreeCoprimeCoreAverageGood p) :
    bothThreeBaseFullBlockZeroAtX0 p :=
  bothThreeBaseFullBlockZeroAtX0_of_coprimeCoreReducedGood hp
    (bothThreeCoprimeCoreReducedGood_of_rawGood_of_averageGood hraw havg)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
