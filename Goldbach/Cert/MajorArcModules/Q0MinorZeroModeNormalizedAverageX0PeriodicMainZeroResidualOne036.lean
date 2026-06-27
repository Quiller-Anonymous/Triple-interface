import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [36,37). -/

theorem periodicMainPair_2733_911_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2733 911 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2733 = ([1, 3, 911, 2733] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 911 = ([1, 911] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2733 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2733 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_911 : ramanujanGcdClassCoeffRat 2733 911 = (-910 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2733 : ramanujanGcdClassCoeffRat 2733 2733 = (1820 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 911 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_911 : ramanujanGcdClassCoeffRat 911 911 = (910 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2733 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2733 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_911 : ramanujanGcdClassWindowAverageRat X0 2733 911 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2733 : ramanujanGcdClassWindowAverageRat X0 2733 2733 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 911 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_911 : ramanujanGcdClassWindowAverageRat X0 911 911 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2733 911 2733 1 = (1820 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2733 911 2733 3 = (910 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_911 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2733 911 2733 911 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2733 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2733 911 2733 2733 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2733 911 911 1 = (2730 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_911 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2733 911 911 911 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2733 911 1 1 = (1820 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_911 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2733 911 1 911 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2733 911 3 1 = (910 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_911 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2733 911 3 911 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_911_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2733 911 911 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_911_911 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2733 911 911 911 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2733_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2733 911 2733 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2733_911 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2733 911 2733 911 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_911, hCoeffLeft_2733, hCoeffRight_1, hCoeffRight_911, hAvgLeft_1, hAvgLeft_3, hAvgLeft_911, hAvgLeft_2733, hAvgRight_1, hAvgRight_911, hBlockLeft_1, hBlockLeft_3, hBlockLeft_911, hBlockLeft_2733, hBlockRight_1, hBlockRight_911, hPair_1_1, hPair_1_911, hPair_3_1, hPair_3_911, hPair_911_1, hPair_911_911, hPair_2733_1, hPair_2733_911]

theorem periodicMainPair_2733_911_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2733 911) = (0 : ℚ) / 1 := by
  have hneq : 2733 ≠ 911 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2733 = (1 : ℚ) / 662480 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 911 = (1 : ℚ) / 165620 := by
    native_decide
  have hvalue : ((1 : ℚ) / 662480) * ((1 : ℚ) / 165620) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2733_911_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne036Pairs : Finset (ℕ × ℕ) :=
  [(2733, 911)].toFinset

theorem PeriodicMainRecordsZeroResidualOne036_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne036Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne036Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2733_911_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
