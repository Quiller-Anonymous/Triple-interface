import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeStructural

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def bothThreeCenteredRawGood (p : ℕ × ℕ) : Prop :=
  rawEvenRamanujanPairBlockSumRat X0 p.1 p.2 = 0
    ∧ rawEvenRamanujanBlockSumRat X0 p.1 p.2 p.1 = 0
    ∧ rawEvenRamanujanBlockSumRat X0 p.1 p.2 p.2 = 0
    ∧ (ramanujanWindowAverageByGcdRat X0 p.1 = 0
        ∨ ramanujanWindowAverageByGcdRat X0 p.2 = 0)
    ∧ 1 ≤ p.1
    ∧ 1 ≤ p.2

instance instDecidableBothThreeCenteredRawGood
    (p : ℕ × ℕ) : Decidable (bothThreeCenteredRawGood p) := by
  unfold bothThreeCenteredRawGood
  infer_instance

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCenteredRawBadPairsInLeftRange
    (lo hi : ℕ) : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs.filter
    (fun p =>
      if lo ≤ p.1 then
        if p.1 < hi then
          ! decide (bothThreeCenteredRawGood p)
        else
          false
      else
        false)

theorem bothThreeCenteredRawGood_of_badPairsInLeftRange_card_zero
    {lo hi : ℕ}
    (hcard :
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCenteredRawBadPairsInLeftRange
        lo hi).card = 0)
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs)
    (hlo : lo ≤ p.1) (hhi : p.1 < hi) :
    bothThreeCenteredRawGood p := by
  by_contra hgood
  have hbad :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCenteredRawBadPairsInLeftRange
        lo hi := by
    exact Finset.mem_filter.mpr ⟨hp, by simp [hlo, hhi, hgood]⟩
  have hempty :
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCenteredRawBadPairsInLeftRange
        lo hi = ∅ :=
    Finset.card_eq_zero.mp hcard
  rw [hempty] at hbad
  simp at hbad

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
