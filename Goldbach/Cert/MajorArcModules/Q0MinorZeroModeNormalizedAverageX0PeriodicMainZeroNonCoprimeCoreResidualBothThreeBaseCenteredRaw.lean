import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeBaseSplit

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Decidable raw witness surface for the `bothThree` odd-core base pair.

This is the fallback certificate shape after dyadic compression.  For each
record `p`, the transport layer only needs the full-block zero of
`(3 * bothThreeOddCore p.1, 3 * bothThreeOddCore p.2)`.  The raw witness below
is decidable and implies that full-block zero through the same centered/raw
decomposition used by the original `BothThreeFinal` module.
-/

def bothThreeBaseCenteredRawGood (p : ℕ × ℕ) : Prop :=
  let q := 3 * bothThreeOddCore p.1
  let q' := 3 * bothThreeOddCore p.2
  rawEvenRamanujanPairBlockSumRat X0 q q' = 0
    ∧ rawEvenRamanujanBlockSumRat X0 q q' q = 0
    ∧ rawEvenRamanujanBlockSumRat X0 q q' q' = 0
    ∧ (ramanujanWindowAverageByGcdRat X0 q = 0
        ∨ ramanujanWindowAverageByGcdRat X0 q' = 0)
    ∧ 1 ≤ q
    ∧ 1 ≤ q'

instance instDecidableBothThreeBaseCenteredRawGood
    (p : ℕ × ℕ) : Decidable (bothThreeBaseCenteredRawGood p) := by
  unfold bothThreeBaseCenteredRawGood
  infer_instance

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeBaseCenteredRawBadPairsInLeftRange
    (lo hi : ℕ) : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs.filter
    (fun p =>
      if lo ≤ p.1 then
        if p.1 < hi then
          ! decide (bothThreeBaseCenteredRawGood p)
        else
          false
      else
        false)

theorem bothThreeBaseCenteredRawGood_of_badPairsInLeftRange_card_zero
    {lo hi : ℕ}
    (hcard :
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeBaseCenteredRawBadPairsInLeftRange
        lo hi).card = 0)
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs)
    (hlo : lo ≤ p.1) (hhi : p.1 < hi) :
    bothThreeBaseCenteredRawGood p := by
  by_contra hgood
  have hbad :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeBaseCenteredRawBadPairsInLeftRange
        lo hi := by
    exact Finset.mem_filter.mpr ⟨hp, by simp [hlo, hhi, hgood]⟩
  have hempty :
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeBaseCenteredRawBadPairsInLeftRange
        lo hi = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hempty] at hbad
  simp at hbad

theorem bothThreeBaseFullBlockZeroAtX0_of_baseCenteredRawGood
    {p : ℕ × ℕ} (hgood : bothThreeBaseCenteredRawGood p) :
    bothThreeBaseFullBlockZeroAtX0 p := by
  let q := 3 * bothThreeOddCore p.1
  let q' := 3 * bothThreeOddCore p.2
  have hgood' :
      rawEvenRamanujanPairBlockSumRat X0 q q' = 0
        ∧ rawEvenRamanujanBlockSumRat X0 q q' q = 0
        ∧ rawEvenRamanujanBlockSumRat X0 q q' q' = 0
        ∧ (ramanujanWindowAverageByGcdRat X0 q = 0
            ∨ ramanujanWindowAverageByGcdRat X0 q' = 0)
        ∧ 1 ≤ q
        ∧ 1 ≤ q' := by
    simpa [bothThreeBaseCenteredRawGood, q, q'] using hgood
  rcases hgood' with ⟨hpair, hleft, hright, havg, hqpos, hq'pos⟩
  unfold bothThreeBaseFullBlockZeroAtX0
  change centeredRamanujanPairFullEvenBlockSum X0 q q' = 0
  rw [centeredRamanujanPairFullEvenBlockSum_eq_rawBlock_decomposition]
  rw [rawEvenRamanujanPairBlockSum_eq_ratCast]
  rw [rawEvenRamanujanBlockSum_eq_ratCast]
  rw [rawEvenRamanujanBlockSum_eq_ratCast]
  rw [hpair, hleft, hright]
  rcases havg with havgLeft | havgRight
  · have havgLeftReal : ramanujanWindowAverage X0 q = 0 := by
      rw [ramanujanWindowAverage_eq_ratCast_ramanujanWindowAverageByGcdRat
        (X := X0) (q := q) hqpos]
      rw [havgLeft]
      norm_num
    rw [havgLeftReal]
    ring
  · have havgRightReal : ramanujanWindowAverage X0 q' = 0 := by
      rw [ramanujanWindowAverage_eq_ratCast_ramanujanWindowAverageByGcdRat
        (X := X0) (q := q') hq'pos]
      rw [havgRight]
      norm_num
    rw [havgRightReal]
    ring

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
