import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [40,41). -/

theorem periodicMainPair_2919_139_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2919 139 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2919 = ([1, 3, 7, 21, 139, 417, 973, 2919] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 139 = ([1, 139] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2919 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2919 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 2919 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_21 : ramanujanGcdClassCoeffRat 2919 21 = (-12 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_139 : ramanujanGcdClassCoeffRat 2919 139 = (138 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_417 : ramanujanGcdClassCoeffRat 2919 417 = (-276 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_973 : ramanujanGcdClassCoeffRat 2919 973 = (-828 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2919 : ramanujanGcdClassCoeffRat 2919 2919 = (1656 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 139 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_139 : ramanujanGcdClassCoeffRat 139 139 = (138 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2919 1 = (946 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2919 3 = (473 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 2919 7 = (472 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_21 : ramanujanGcdClassWindowAverageRat X0 2919 21 = (236 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_139 : ramanujanGcdClassWindowAverageRat X0 2919 139 = (20 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_417 : ramanujanGcdClassWindowAverageRat X0 2919 417 = (10 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_973 : ramanujanGcdClassWindowAverageRat X0 2919 973 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2919 : ramanujanGcdClassWindowAverageRat X0 2919 2919 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 139 1 = (1655 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_139 : ramanujanGcdClassWindowAverageRat X0 139 139 = (12 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 2919 1 = (1656 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 2919 3 = (828 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 2919 7 = (276 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 2919 21 = (138 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_139 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 2919 139 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_417 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 2919 417 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_973 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 2919 973 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2919 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 2919 2919 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 139 1 = (2898 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_139 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2919 139 139 139 = (21 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 1 1 = (1656 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 1 139 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 3 1 = (828 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 3 139 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 7 1 = (276 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 7 139 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 21 1 = (138 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 21 139 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 139 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 139 139 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_417_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 417 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_417_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 417 139 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 973 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 973 139 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2919_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 2919 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2919_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2919 139 2919 139 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_7, hCoeffLeft_21, hCoeffLeft_139, hCoeffLeft_417, hCoeffLeft_973, hCoeffLeft_2919, hCoeffRight_1, hCoeffRight_139, hAvgLeft_1, hAvgLeft_3, hAvgLeft_7, hAvgLeft_21, hAvgLeft_139, hAvgLeft_417, hAvgLeft_973, hAvgLeft_2919, hAvgRight_1, hAvgRight_139, hBlockLeft_1, hBlockLeft_3, hBlockLeft_7, hBlockLeft_21, hBlockLeft_139, hBlockLeft_417, hBlockLeft_973, hBlockLeft_2919, hBlockRight_1, hBlockRight_139, hPair_1_1, hPair_1_139, hPair_3_1, hPair_3_139, hPair_7_1, hPair_7_139, hPair_21_1, hPair_21_139, hPair_139_1, hPair_139_139, hPair_417_1, hPair_417_139, hPair_973_1, hPair_973_139, hPair_2919_1, hPair_2919_139]

theorem periodicMainPair_2919_139_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2919 139) = (0 : ℚ) / 1 := by
  have hneq : 2919 ≠ 139 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2919 = (5 : ℚ) / 2742336 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 139 = (5 : ℚ) / 19044 := by
    native_decide
  have hvalue : ((5 : ℚ) / 2742336) * ((5 : ℚ) / 19044) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2919_139_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne040Pairs : Finset (ℕ × ℕ) :=
  [(2919, 139)].toFinset

theorem PeriodicMainRecordsZeroResidualOne040_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne040Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne040Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2919_139_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
