import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [28,29). -/

theorem periodicMainPair_2559_853_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2559 853 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2559 = ([1, 3, 853, 2559] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 853 = ([1, 853] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2559 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2559 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_853 : ramanujanGcdClassCoeffRat 2559 853 = (-852 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2559 : ramanujanGcdClassCoeffRat 2559 2559 = (1704 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 853 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_853 : ramanujanGcdClassCoeffRat 853 853 = (852 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2559 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2559 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_853 : ramanujanGcdClassWindowAverageRat X0 2559 853 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2559 : ramanujanGcdClassWindowAverageRat X0 2559 2559 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 853 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_853 : ramanujanGcdClassWindowAverageRat X0 853 853 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2559 853 2559 1 = (1704 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2559 853 2559 3 = (852 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_853 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2559 853 2559 853 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2559 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2559 853 2559 2559 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2559 853 853 1 = (2556 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_853 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2559 853 853 853 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2559 853 1 1 = (1704 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_853 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2559 853 1 853 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2559 853 3 1 = (852 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_853 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2559 853 3 853 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_853_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2559 853 853 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_853_853 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2559 853 853 853 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2559_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2559 853 2559 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2559_853 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2559 853 2559 853 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_853, hCoeffLeft_2559, hCoeffRight_1, hCoeffRight_853, hAvgLeft_1, hAvgLeft_3, hAvgLeft_853, hAvgLeft_2559, hAvgRight_1, hAvgRight_853, hBlockLeft_1, hBlockLeft_3, hBlockLeft_853, hBlockLeft_2559, hBlockRight_1, hBlockRight_853, hPair_1_1, hPair_1_853, hPair_3_1, hPair_3_853, hPair_853_1, hPair_853_853, hPair_2559_1, hPair_2559_853]

theorem periodicMainPair_2559_853_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2559 853) = (0 : ℚ) / 1 := by
  have hneq : 2559 ≠ 853 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2559 = (5 : ℚ) / 2903616 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 853 = (5 : ℚ) / 725904 := by
    native_decide
  have hvalue : ((5 : ℚ) / 2903616) * ((5 : ℚ) / 725904) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2559_853_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne028Pairs : Finset (ℕ × ℕ) :=
  [(2559, 853)].toFinset

theorem PeriodicMainRecordsZeroResidualOne028_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne028Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne028Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2559_853_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
