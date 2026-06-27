import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [0,3). -/

theorem periodicMainPair_7_2667_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 7 2667 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 7 = ([1, 7] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 2667 = ([1, 3, 7, 21, 127, 381, 889, 2667] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 7 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 2667 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 2667 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 2667 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_21 : ramanujanGcdClassCoeffRat 2667 21 = (-12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_127 : ramanujanGcdClassCoeffRat 2667 127 = (126 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_381 : ramanujanGcdClassCoeffRat 2667 381 = (-252 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_889 : ramanujanGcdClassCoeffRat 2667 889 = (-756 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2667 : ramanujanGcdClassCoeffRat 2667 2667 = (1512 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 7 7 = (238 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 2667 1 = (2836 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 2667 3 = (1418 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 2667 7 = (472 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_21 : ramanujanGcdClassWindowAverageRat X0 2667 21 = (236 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_127 : ramanujanGcdClassWindowAverageRat X0 2667 127 = (22 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_381 : ramanujanGcdClassWindowAverageRat X0 2667 381 = (11 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_889 : ramanujanGcdClassWindowAverageRat X0 2667 889 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_2667 : ramanujanGcdClassWindowAverageRat X0 2667 2667 = (2 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 7 1 = (2286 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 7 7 = (381 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 2667 1 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 2667 3 = (756 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 2667 7 = (252 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 2667 21 = (126 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_127 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 2667 127 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_381 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 2667 381 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_889 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 2667 889 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_2667 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2667 2667 2667 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 1 1 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 1 3 = (756 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 1 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 1 127 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_381 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 1 381 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 1 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2667 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 1 2667 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 7 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 7 7 = (252 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 7 21 = (126 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 7 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_381 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 7 381 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 7 889 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_2667 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2667 7 2667 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_7, hCoeffRight_1, hCoeffRight_3, hCoeffRight_7, hCoeffRight_21, hCoeffRight_127, hCoeffRight_381, hCoeffRight_889, hCoeffRight_2667, hAvgLeft_1, hAvgLeft_7, hAvgRight_1, hAvgRight_3, hAvgRight_7, hAvgRight_21, hAvgRight_127, hAvgRight_381, hAvgRight_889, hAvgRight_2667, hBlockLeft_1, hBlockLeft_7, hBlockRight_1, hBlockRight_3, hBlockRight_7, hBlockRight_21, hBlockRight_127, hBlockRight_381, hBlockRight_889, hBlockRight_2667, hPair_1_1, hPair_1_3, hPair_1_7, hPair_1_21, hPair_1_127, hPair_1_381, hPair_1_889, hPair_1_2667, hPair_7_1, hPair_7_3, hPair_7_7, hPair_7_21, hPair_7_127, hPair_7_381, hPair_7_889, hPair_7_2667]

theorem periodicMainPair_7_2667_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 7 2667) = (0 : ℚ) / 1 := by
  have hneq : 7 ≠ 2667 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 7 = (5 : ℚ) / 36 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 2667 = (5 : ℚ) / 2286144 := by
    native_decide
  have hvalue : ((5 : ℚ) / 36) * ((5 : ℚ) / 2286144) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_7_2667_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_7_2919_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 7 2919 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 7 = ([1, 7] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 2919 = ([1, 3, 7, 21, 139, 417, 973, 2919] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 7 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 2919 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 2919 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 2919 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_21 : ramanujanGcdClassCoeffRat 2919 21 = (-12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_139 : ramanujanGcdClassCoeffRat 2919 139 = (138 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_417 : ramanujanGcdClassCoeffRat 2919 417 = (-276 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_973 : ramanujanGcdClassCoeffRat 2919 973 = (-828 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2919 : ramanujanGcdClassCoeffRat 2919 2919 = (1656 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 7 7 = (238 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 2919 1 = (946 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 2919 3 = (473 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 2919 7 = (472 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_21 : ramanujanGcdClassWindowAverageRat X0 2919 21 = (236 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_139 : ramanujanGcdClassWindowAverageRat X0 2919 139 = (20 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_417 : ramanujanGcdClassWindowAverageRat X0 2919 417 = (10 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_973 : ramanujanGcdClassWindowAverageRat X0 2919 973 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_2919 : ramanujanGcdClassWindowAverageRat X0 2919 2919 = (2 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 7 1 = (2502 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 7 7 = (417 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 2919 1 = (1656 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 2919 3 = (828 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 2919 7 = (276 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 2919 21 = (138 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_139 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 2919 139 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_417 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 2919 417 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_973 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 2919 973 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_2919 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 2919 2919 2919 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 1 1 = (1656 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 1 3 = (828 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 1 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 1 139 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_417 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 1 417 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_973 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 1 973 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2919 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 1 2919 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 7 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 7 7 = (276 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 7 21 = (138 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 7 139 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_417 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 7 417 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_973 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 7 973 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_2919 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 2919 7 2919 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_7, hCoeffRight_1, hCoeffRight_3, hCoeffRight_7, hCoeffRight_21, hCoeffRight_139, hCoeffRight_417, hCoeffRight_973, hCoeffRight_2919, hAvgLeft_1, hAvgLeft_7, hAvgRight_1, hAvgRight_3, hAvgRight_7, hAvgRight_21, hAvgRight_139, hAvgRight_417, hAvgRight_973, hAvgRight_2919, hBlockLeft_1, hBlockLeft_7, hBlockRight_1, hBlockRight_3, hBlockRight_7, hBlockRight_21, hBlockRight_139, hBlockRight_417, hBlockRight_973, hBlockRight_2919, hPair_1_1, hPair_1_3, hPair_1_7, hPair_1_21, hPair_1_139, hPair_1_417, hPair_1_973, hPair_1_2919, hPair_7_1, hPair_7_3, hPair_7_7, hPair_7_21, hPair_7_139, hPair_7_417, hPair_7_973, hPair_7_2919]

theorem periodicMainPair_7_2919_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 7 2919) = (0 : ℚ) / 1 := by
  have hneq : 7 ≠ 2919 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 7 = (5 : ℚ) / 36 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 2919 = (5 : ℚ) / 2742336 := by
    native_decide
  have hvalue : ((5 : ℚ) / 36) * ((5 : ℚ) / 2742336) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_7_2919_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_7_4431_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 7 4431 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 7 = ([1, 7] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 4431 = ([1, 3, 7, 21, 211, 633, 1477, 4431] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 7 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 4431 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 4431 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 4431 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_21 : ramanujanGcdClassCoeffRat 4431 21 = (-12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_211 : ramanujanGcdClassCoeffRat 4431 211 = (210 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_633 : ramanujanGcdClassCoeffRat 4431 633 = (-420 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1477 : ramanujanGcdClassCoeffRat 4431 1477 = (-1260 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_4431 : ramanujanGcdClassCoeffRat 4431 4431 = (2520 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 7 7 = (238 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 4431 1 = (948 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 4431 3 = (474 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 4431 7 = (158 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_21 : ramanujanGcdClassWindowAverageRat X0 4431 21 = (79 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_211 : ramanujanGcdClassWindowAverageRat X0 4431 211 = (14 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_633 : ramanujanGcdClassWindowAverageRat X0 4431 633 = (7 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1477 : ramanujanGcdClassWindowAverageRat X0 4431 1477 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_4431 : ramanujanGcdClassWindowAverageRat X0 4431 4431 = (1 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 7 1 = (3798 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 7 7 = (633 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 3 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 7 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 21 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_211 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 211 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_633 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 633 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1477 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 1477 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_4431 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 4431 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 3 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 211 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_633 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 633 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_1477 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 1477 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_4431 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 4431 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 7 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 21 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 211 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_633 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 633 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1477 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 1477 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_4431 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 4431 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_7, hCoeffRight_1, hCoeffRight_3, hCoeffRight_7, hCoeffRight_21, hCoeffRight_211, hCoeffRight_633, hCoeffRight_1477, hCoeffRight_4431, hAvgLeft_1, hAvgLeft_7, hAvgRight_1, hAvgRight_3, hAvgRight_7, hAvgRight_21, hAvgRight_211, hAvgRight_633, hAvgRight_1477, hAvgRight_4431, hBlockLeft_1, hBlockLeft_7, hBlockRight_1, hBlockRight_3, hBlockRight_7, hBlockRight_21, hBlockRight_211, hBlockRight_633, hBlockRight_1477, hBlockRight_4431, hPair_1_1, hPair_1_3, hPair_1_7, hPair_1_21, hPair_1_211, hPair_1_633, hPair_1_1477, hPair_1_4431, hPair_7_1, hPair_7_3, hPair_7_7, hPair_7_21, hPair_7_211, hPair_7_633, hPair_7_1477, hPair_7_4431]

theorem periodicMainPair_7_4431_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 7 4431) = (0 : ℚ) / 1 := by
  have hneq : 7 ≠ 4431 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 7 = (5 : ℚ) / 36 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 4431 = (1 : ℚ) / 1270080 := by
    native_decide
  have hvalue : ((5 : ℚ) / 36) * ((1 : ℚ) / 1270080) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_7_4431_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualChunk000Pairs : Finset (ℕ × ℕ) :=
  [(7, 2667), (7, 2919), (7, 4431)].toFinset

theorem PeriodicMainRecordsZeroResidualChunk000_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualChunk000Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualChunk000Pairs] at hp
  rcases hp with h | h | h
  · subst p
    simpa using periodicMainPair_7_2667_X1000000_orderedSummand
  · subst p
    simpa using periodicMainPair_7_2919_X1000000_orderedSummand
  · subst p
    simpa using periodicMainPair_7_4431_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
