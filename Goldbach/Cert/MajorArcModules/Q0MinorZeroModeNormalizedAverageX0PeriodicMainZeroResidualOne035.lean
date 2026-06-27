import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [35,36). -/

theorem periodicMainPair_2667_889_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2667 889 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2667 = ([1, 3, 7, 21, 127, 381, 889, 2667] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 889 = ([1, 7, 127, 889] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2667 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2667 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 2667 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_21 : ramanujanGcdClassCoeffRat 2667 21 = (-12 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_127 : ramanujanGcdClassCoeffRat 2667 127 = (126 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_381 : ramanujanGcdClassCoeffRat 2667 381 = (-252 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_889 : ramanujanGcdClassCoeffRat 2667 889 = (-756 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2667 : ramanujanGcdClassCoeffRat 2667 2667 = (1512 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 889 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 889 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_127 : ramanujanGcdClassCoeffRat 889 127 = (-126 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_889 : ramanujanGcdClassCoeffRat 889 889 = (756 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2667 1 = (2836 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2667 3 = (1418 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 2667 7 = (472 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_21 : ramanujanGcdClassWindowAverageRat X0 2667 21 = (236 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_127 : ramanujanGcdClassWindowAverageRat X0 2667 127 = (22 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_381 : ramanujanGcdClassWindowAverageRat X0 2667 381 = (11 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_889 : ramanujanGcdClassWindowAverageRat X0 2667 889 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2667 : ramanujanGcdClassWindowAverageRat X0 2667 2667 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 889 1 = (1418 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 889 7 = (236 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_127 : ramanujanGcdClassWindowAverageRat X0 889 127 = (11 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_889 : ramanujanGcdClassWindowAverageRat X0 889 889 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 2667 1 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 2667 3 = (756 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 2667 7 = (252 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 2667 21 = (126 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_127 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 2667 127 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_381 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 2667 381 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_889 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 2667 889 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2667 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 2667 2667 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 889 1 = (2268 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 889 7 = (378 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_127 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 889 127 = (18 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_889 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2667 889 889 889 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 1 1 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 1 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 1 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 3 1 = (756 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 3 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 3 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 3 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 7 7 = (252 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 7 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 7 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 21 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 21 7 = (126 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 21 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 21 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 127 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 127 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 127 127 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 127 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_381_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 381 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_381_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 381 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_381_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 381 127 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_381_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 381 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 889 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 889 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 889 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 889 889 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2667_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 2667 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2667_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 2667 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2667_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 2667 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2667_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2667 889 2667 889 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_7, hCoeffLeft_21, hCoeffLeft_127, hCoeffLeft_381, hCoeffLeft_889, hCoeffLeft_2667, hCoeffRight_1, hCoeffRight_7, hCoeffRight_127, hCoeffRight_889, hAvgLeft_1, hAvgLeft_3, hAvgLeft_7, hAvgLeft_21, hAvgLeft_127, hAvgLeft_381, hAvgLeft_889, hAvgLeft_2667, hAvgRight_1, hAvgRight_7, hAvgRight_127, hAvgRight_889, hBlockLeft_1, hBlockLeft_3, hBlockLeft_7, hBlockLeft_21, hBlockLeft_127, hBlockLeft_381, hBlockLeft_889, hBlockLeft_2667, hBlockRight_1, hBlockRight_7, hBlockRight_127, hBlockRight_889, hPair_1_1, hPair_1_7, hPair_1_127, hPair_1_889, hPair_3_1, hPair_3_7, hPair_3_127, hPair_3_889, hPair_7_1, hPair_7_7, hPair_7_127, hPair_7_889, hPair_21_1, hPair_21_7, hPair_21_127, hPair_21_889, hPair_127_1, hPair_127_7, hPair_127_127, hPair_127_889, hPair_381_1, hPair_381_7, hPair_381_127, hPair_381_889, hPair_889_1, hPair_889_7, hPair_889_127, hPair_889_889, hPair_2667_1, hPair_2667_7, hPair_2667_127, hPair_2667_889]

theorem periodicMainPair_2667_889_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2667 889) = (0 : ℚ) / 1 := by
  have hneq : 2667 ≠ 889 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2667 = (5 : ℚ) / 2286144 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 889 = (5 : ℚ) / 571536 := by
    native_decide
  have hvalue : ((5 : ℚ) / 2286144) * ((5 : ℚ) / 571536) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2667_889_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne035Pairs : Finset (ℕ × ℕ) :=
  [(2667, 889)].toFinset

theorem PeriodicMainRecordsZeroResidualOne035_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne035Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne035Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2667_889_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
