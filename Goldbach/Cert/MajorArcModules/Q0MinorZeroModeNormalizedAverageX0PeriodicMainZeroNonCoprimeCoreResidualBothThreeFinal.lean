import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeStructural

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

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

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCenteredRawBadPairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs.filter
    (fun p => ! decide (bothThreeCenteredRawGood p))

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCenteredRawBadPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCenteredRawBadPairs.card = 0 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_centeredRaw_good :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      bothThreeCenteredRawGood p := by
  exact forall_mem_of_bad_filter_card_zero (s :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs)
    (P := bothThreeCenteredRawGood)
    (by
      simpa [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCenteredRawBadPairs]
        using PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCenteredRawBadPairs_card)

theorem centeredRamanujanPairFullEvenBlockSum_X0_eq_zero_of_bothThreeCenteredRawGood
    {q q' : ℕ} (hgood : bothThreeCenteredRawGood (q, q')) :
    centeredRamanujanPairFullEvenBlockSum X0 q q' = 0 := by
  rcases hgood with ⟨hpair, hleft, hright, havg, hqpos, hq'pos⟩
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

theorem centeredRamanujanPairPeriodicMainTerm_X0_eq_zero_of_bothThreeCenteredRawGood
    {q q' : ℕ} (hgood : bothThreeCenteredRawGood (q, q')) :
    centeredRamanujanPairPeriodicMainTerm X0 q q' = 0 := by
  rcases hgood with ⟨hpair, hleft, hright, havg, hqpos, hq'pos⟩
  have hgood' : bothThreeCenteredRawGood (q, q') :=
    ⟨hpair, hleft, hright, havg, hqpos, hq'pos⟩
  rw [centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_bothThree_probe
    (X := X0) (q := q) (q' := q') hqpos hq'pos]
  rw [centeredRamanujanPairFullEvenBlockSum_X0_eq_zero_of_bothThreeCenteredRawGood hgood']
  simp

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  have hgood :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_centeredRaw_good p hp
  have hterm :
      centeredRamanujanPairPeriodicMainTerm X0 p.1 p.2 = 0 := by
    simpa using
      centeredRamanujanPairPeriodicMainTerm_X0_eq_zero_of_bothThreeCenteredRawGood
        (q := p.1) (q' := p.2) hgood
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · simp [hdiag, hterm]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
