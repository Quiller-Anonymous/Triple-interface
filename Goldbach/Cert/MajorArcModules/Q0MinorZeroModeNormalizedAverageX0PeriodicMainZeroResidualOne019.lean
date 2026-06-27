import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [19,20). -/

theorem periodicMainPair_911_2733_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 911 2733 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 911 = ([1, 911] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 2733 = ([1, 3, 911, 2733] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 911 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_911 : ramanujanGcdClassCoeffRat 911 911 = (910 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 2733 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 2733 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_911 : ramanujanGcdClassCoeffRat 2733 911 = (-910 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2733 : ramanujanGcdClassCoeffRat 2733 2733 = (1820 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 911 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_911 : ramanujanGcdClassWindowAverageRat X0 911 911 = (2 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 2733 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 2733 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_911 : ramanujanGcdClassWindowAverageRat X0 2733 911 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_2733 : ramanujanGcdClassWindowAverageRat X0 2733 2733 = (2 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 911 2733 911 1 = (2730 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_911 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 911 2733 911 911 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 911 2733 2733 1 = (1820 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 911 2733 2733 3 = (910 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_911 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 911 2733 2733 911 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_2733 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 911 2733 2733 2733 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 911 2733 1 1 = (1820 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 911 2733 1 3 = (910 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_911 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 911 2733 1 911 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2733 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 911 2733 1 2733 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_911_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 911 2733 911 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_911_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 911 2733 911 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_911_911 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 911 2733 911 911 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_911_2733 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 911 2733 911 2733 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_911, hCoeffRight_1, hCoeffRight_3, hCoeffRight_911, hCoeffRight_2733, hAvgLeft_1, hAvgLeft_911, hAvgRight_1, hAvgRight_3, hAvgRight_911, hAvgRight_2733, hBlockLeft_1, hBlockLeft_911, hBlockRight_1, hBlockRight_3, hBlockRight_911, hBlockRight_2733, hPair_1_1, hPair_1_3, hPair_1_911, hPair_1_2733, hPair_911_1, hPair_911_3, hPair_911_911, hPair_911_2733]

theorem periodicMainPair_911_2733_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 911 2733) = (0 : ℚ) / 1 := by
  have hneq : 911 ≠ 2733 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 911 = (1 : ℚ) / 165620 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 2733 = (1 : ℚ) / 662480 := by
    native_decide
  have hvalue : ((1 : ℚ) / 165620) * ((1 : ℚ) / 662480) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_911_2733_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne019Pairs : Finset (ℕ × ℕ) :=
  [(911, 2733)].toFinset

theorem PeriodicMainRecordsZeroResidualOne019_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne019Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne019Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_911_2733_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
