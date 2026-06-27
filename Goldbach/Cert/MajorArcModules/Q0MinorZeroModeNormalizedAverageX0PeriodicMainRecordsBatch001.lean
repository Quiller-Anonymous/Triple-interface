import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [0,10). -/

theorem periodicMainPair_3_6_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 3 6 = (9996 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 3 = ([1, 3] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 6 = ([1, 2, 3, 6] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 3 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 3 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 6 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2 : ramanujanGcdClassCoeffRat 6 2 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 6 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_6 : ramanujanGcdClassCoeffRat 6 6 = (2 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 3 1 = (2 : ℚ) / 3 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 3 3 = (1 : ℚ) / 3 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 6 1 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_2 : ramanujanGcdClassWindowAverageRat X0 6 2 = (2 : ℚ) / 3 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 6 3 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_6 : ramanujanGcdClassWindowAverageRat X0 6 6 = (1 : ℚ) / 3 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 3 6 3 1 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 3 6 3 3 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 3 6 6 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_2 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 3 6 6 2 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 3 6 6 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_6 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 3 6 6 6 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 3 6 1 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 3 6 1 2 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 3 6 1 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_6 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 3 6 1 6 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 3 6 3 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 3 6 3 2 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 3 6 3 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_6 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 3 6 3 6 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffRight_1, hCoeffRight_2, hCoeffRight_3, hCoeffRight_6, hAvgLeft_1, hAvgLeft_3, hAvgRight_1, hAvgRight_2, hAvgRight_3, hAvgRight_6, hBlockLeft_1, hBlockLeft_3, hBlockRight_1, hBlockRight_2, hBlockRight_3, hBlockRight_6, hPair_1_1, hPair_1_2, hPair_1_3, hPair_1_6, hPair_3_1, hPair_3_2, hPair_3_3, hPair_3_6]

theorem periodicMainPair_3_6_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 3 6) = (62475 : ℚ) / 4 := by
  have hneq : 3 ≠ 6 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 3 = (5 : ℚ) / 4 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 6 = (5 : ℚ) / 4 := by
    native_decide
  have hvalue : ((5 : ℚ) / 4) * ((5 : ℚ) / 4) * ((9996 : ℚ) / 1) = (62475 : ℚ) / 4 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_3_6_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_5_7_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 5 7 = (-19880 : ℚ) / 8336667 := by
  have hDivLeft : Nat.divisors 5 = ([1, 5] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 7 = ([1, 7] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 5 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_5 : ramanujanGcdClassCoeffRat 5 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 7 7 = (6 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 5 1 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_5 : ramanujanGcdClassWindowAverageRat X0 5 5 = (1001 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 7 7 = (238 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 7 5 1 = (28 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 7 5 5 = (7 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 7 7 1 = (30 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 7 7 7 = (5 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 7 1 1 = (24 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 7 1 7 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 7 5 1 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 7 5 7 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_5, hCoeffRight_1, hCoeffRight_7, hAvgLeft_1, hAvgLeft_5, hAvgRight_1, hAvgRight_7, hBlockLeft_1, hBlockLeft_5, hBlockRight_1, hBlockRight_7, hPair_1_1, hPair_1_7, hPair_5_1, hPair_5_7]

theorem periodicMainPair_5_7_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 5 7) = (-62125 : ℚ) / 600240024 := by
  have hneq : 5 ≠ 7 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 5 = (5 : ℚ) / 16 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 7 = (5 : ℚ) / 36 := by
    native_decide
  have hvalue : ((5 : ℚ) / 16) * ((5 : ℚ) / 36) * ((-19880 : ℚ) / 8336667) = (-62125 : ℚ) / 600240024 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_5_7_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_5_10_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 5 10 = (500200100000 : ℚ) / 25010001 := by
  have hDivLeft : Nat.divisors 5 = ([1, 5] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 10 = ([1, 2, 5, 10] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 5 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_5 : ramanujanGcdClassCoeffRat 5 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 10 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2 : ramanujanGcdClassCoeffRat 10 2 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_5 : ramanujanGcdClassCoeffRat 10 5 = (-4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_10 : ramanujanGcdClassCoeffRat 10 10 = (4 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 5 1 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_5 : ramanujanGcdClassWindowAverageRat X0 5 5 = (1001 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 10 1 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_2 : ramanujanGcdClassWindowAverageRat X0 10 2 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_5 : ramanujanGcdClassWindowAverageRat X0 10 5 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_10 : ramanujanGcdClassWindowAverageRat X0 10 10 = (1001 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 10 5 1 = (8 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 10 5 5 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 10 10 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_2 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 10 10 2 = (8 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 10 10 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_10 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 10 10 10 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 10 1 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 10 1 2 = (8 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 10 1 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_10 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 10 1 10 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 10 5 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 10 5 2 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 10 5 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_10 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 10 5 10 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_5, hCoeffRight_1, hCoeffRight_2, hCoeffRight_5, hCoeffRight_10, hAvgLeft_1, hAvgLeft_5, hAvgRight_1, hAvgRight_2, hAvgRight_5, hAvgRight_10, hBlockLeft_1, hBlockLeft_5, hBlockRight_1, hBlockRight_2, hBlockRight_5, hBlockRight_10, hPair_1_1, hPair_1_2, hPair_1_5, hPair_1_10, hPair_5_1, hPair_5_2, hPair_5_5, hPair_5_10]

theorem periodicMainPair_5_10_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 5 10) = (390781328125 : ℚ) / 200080008 := by
  have hneq : 5 ≠ 10 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 5 = (5 : ℚ) / 16 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 10 = (5 : ℚ) / 16 := by
    native_decide
  have hvalue : ((5 : ℚ) / 16) * ((5 : ℚ) / 16) * ((500200100000 : ℚ) / 25010001) = (390781328125 : ℚ) / 200080008 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_5_10_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_5_11_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 5 11 = (8800 : ℚ) / 2778889 := by
  have hDivLeft : Nat.divisors 5 = ([1, 5] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 11 = ([1, 11] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 5 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_5 : ramanujanGcdClassCoeffRat 5 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 11 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_11 : ramanujanGcdClassCoeffRat 11 11 = (10 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 5 1 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_5 : ramanujanGcdClassWindowAverageRat X0 5 5 = (1001 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 11 1 = (4546 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_11 : ramanujanGcdClassWindowAverageRat X0 11 11 = (455 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 11 5 1 = (44 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 11 5 5 = (11 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 11 11 1 = (50 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_11 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 11 11 11 = (5 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 11 1 1 = (40 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_11 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 11 1 11 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 11 5 1 = (10 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_11 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 11 5 11 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_5, hCoeffRight_1, hCoeffRight_11, hAvgLeft_1, hAvgLeft_5, hAvgRight_1, hAvgRight_11, hBlockLeft_1, hBlockLeft_5, hBlockRight_1, hBlockRight_11, hPair_1_1, hPair_1_11, hPair_5_1, hPair_5_11]

theorem periodicMainPair_5_11_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 5 11) = (275 : ℚ) / 5557778 := by
  have hneq : 5 ≠ 11 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 5 = (5 : ℚ) / 16 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 11 = (1 : ℚ) / 20 := by
    native_decide
  have hvalue : ((5 : ℚ) / 16) * ((1 : ℚ) / 20) * ((8800 : ℚ) / 2778889) = (275 : ℚ) / 5557778 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_5_11_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_5_13_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 5 13 = (79040 : ℚ) / 25010001 := by
  have hDivLeft : Nat.divisors 5 = ([1, 5] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 13 = ([1, 13] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 5 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_5 : ramanujanGcdClassCoeffRat 5 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 13 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_13 : ramanujanGcdClassCoeffRat 13 13 = (12 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 5 1 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_5 : ramanujanGcdClassWindowAverageRat X0 5 5 = (1001 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 13 1 = (4616 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_13 : ramanujanGcdClassWindowAverageRat X0 13 13 = (385 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 13 5 1 = (52 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 13 5 5 = (13 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 13 13 1 = (60 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_13 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 13 13 13 = (5 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 13 1 1 = (48 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_13 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 13 1 13 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 13 5 1 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_13 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 13 5 13 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_5, hCoeffRight_1, hCoeffRight_13, hAvgLeft_1, hAvgLeft_5, hAvgRight_1, hAvgRight_13, hBlockLeft_1, hBlockLeft_5, hBlockRight_1, hBlockRight_13, hPair_1_1, hPair_1_13, hPair_5_1, hPair_5_13]

theorem periodicMainPair_5_13_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 5 13) = (30875 : ℚ) / 900360036 := by
  have hneq : 5 ≠ 13 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 5 = (5 : ℚ) / 16 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 13 = (5 : ℚ) / 144 := by
    native_decide
  have hvalue : ((5 : ℚ) / 16) * ((5 : ℚ) / 144) * ((79040 : ℚ) / 25010001) = (30875 : ℚ) / 900360036 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_5_13_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_5_14_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 5 14 = (-19880 : ℚ) / 8336667 := by
  have hDivLeft : Nat.divisors 5 = ([1, 5] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 14 = ([1, 2, 7, 14] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 5 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_5 : ramanujanGcdClassCoeffRat 5 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 14 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2 : ramanujanGcdClassCoeffRat 14 2 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 14 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_14 : ramanujanGcdClassCoeffRat 14 14 = (6 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 5 1 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_5 : ramanujanGcdClassWindowAverageRat X0 5 5 = (1001 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 14 1 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_2 : ramanujanGcdClassWindowAverageRat X0 14 2 = (1429 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 14 7 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_14 : ramanujanGcdClassWindowAverageRat X0 14 14 = (238 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 14 5 1 = (56 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 14 5 5 = (14 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 14 14 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_2 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 14 14 2 = (60 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 14 14 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_14 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 14 14 14 = (10 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 14 1 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 14 1 2 = (48 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 14 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 14 1 14 = (8 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 14 5 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 14 5 2 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 14 5 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 14 5 14 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_5, hCoeffRight_1, hCoeffRight_2, hCoeffRight_7, hCoeffRight_14, hAvgLeft_1, hAvgLeft_5, hAvgRight_1, hAvgRight_2, hAvgRight_7, hAvgRight_14, hBlockLeft_1, hBlockLeft_5, hBlockRight_1, hBlockRight_2, hBlockRight_7, hBlockRight_14, hPair_1_1, hPair_1_2, hPair_1_7, hPair_1_14, hPair_5_1, hPair_5_2, hPair_5_7, hPair_5_14]

theorem periodicMainPair_5_14_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 5 14) = (-62125 : ℚ) / 600240024 := by
  have hneq : 5 ≠ 14 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 5 = (5 : ℚ) / 16 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 14 = (5 : ℚ) / 36 := by
    native_decide
  have hvalue : ((5 : ℚ) / 16) * ((5 : ℚ) / 36) * ((-19880 : ℚ) / 8336667) = (-62125 : ℚ) / 600240024 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_5_14_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_5_15_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 5 15 = (-22200 : ℚ) / 2778889 := by
  have hDivLeft : Nat.divisors 5 = ([1, 5] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 15 = ([1, 3, 5, 15] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 5 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_5 : ramanujanGcdClassCoeffRat 5 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 15 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 15 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_5 : ramanujanGcdClassCoeffRat 15 5 = (-4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_15 : ramanujanGcdClassCoeffRat 15 15 = (8 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 5 1 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_5 : ramanujanGcdClassWindowAverageRat X0 5 5 = (1001 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 15 1 = (2666 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 15 3 = (1334 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_5 : ramanujanGcdClassWindowAverageRat X0 15 5 = (668 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_15 : ramanujanGcdClassWindowAverageRat X0 15 15 = (111 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 15 5 1 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 15 5 5 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 15 15 1 = (8 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 15 15 3 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 15 15 5 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_15 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 15 15 15 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 15 1 1 = (8 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 15 1 3 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 15 1 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_15 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 15 1 15 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 15 5 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 15 5 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 15 5 5 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_15 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 15 5 15 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_5, hCoeffRight_1, hCoeffRight_3, hCoeffRight_5, hCoeffRight_15, hAvgLeft_1, hAvgLeft_5, hAvgRight_1, hAvgRight_3, hAvgRight_5, hAvgRight_15, hBlockLeft_1, hBlockLeft_5, hBlockRight_1, hBlockRight_3, hBlockRight_5, hBlockRight_15, hPair_1_1, hPair_1_3, hPair_1_5, hPair_1_15, hPair_5_1, hPair_5_3, hPair_5_5, hPair_5_15]

theorem periodicMainPair_5_15_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 5 15) = (-69375 : ℚ) / 355697792 := by
  have hneq : 5 ≠ 15 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 5 = (5 : ℚ) / 16 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 15 = (5 : ℚ) / 64 := by
    native_decide
  have hvalue : ((5 : ℚ) / 16) * ((5 : ℚ) / 64) * ((-22200 : ℚ) / 2778889) = (-69375 : ℚ) / 355697792 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_5_15_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_5_17_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 5 17 = (-19720 : ℚ) / 8336667 := by
  have hDivLeft : Nat.divisors 5 = ([1, 5] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 17 = ([1, 17] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 5 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_5 : ramanujanGcdClassCoeffRat 5 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 17 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_17 : ramanujanGcdClassCoeffRat 17 17 = (16 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 5 1 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_5 : ramanujanGcdClassWindowAverageRat X0 5 5 = (1001 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 17 1 = (1569 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_17 : ramanujanGcdClassWindowAverageRat X0 17 17 = (98 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 17 5 1 = (68 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 17 5 5 = (17 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 17 17 1 = (80 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_17 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 17 17 17 = (5 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 17 1 1 = (64 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 17 1 17 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 17 5 1 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 17 5 17 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_5, hCoeffRight_1, hCoeffRight_17, hAvgLeft_1, hAvgLeft_5, hAvgRight_1, hAvgRight_17, hBlockLeft_1, hBlockLeft_5, hBlockRight_1, hBlockRight_17, hPair_1_1, hPair_1_17, hPair_5_1, hPair_5_17]

theorem periodicMainPair_5_17_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 5 17) = (-61625 : ℚ) / 4268373504 := by
  have hneq : 5 ≠ 17 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 5 = (5 : ℚ) / 16 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 17 = (5 : ℚ) / 256 := by
    native_decide
  have hvalue : ((5 : ℚ) / 16) * ((5 : ℚ) / 256) * ((-19720 : ℚ) / 8336667) = (-61625 : ℚ) / 4268373504 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_5_17_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_5_19_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 5 19 = (-79040 : ℚ) / 25010001 := by
  have hDivLeft : Nat.divisors 5 = ([1, 5] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 19 = ([1, 19] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 5 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_5 : ramanujanGcdClassCoeffRat 5 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 19 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_19 : ramanujanGcdClassCoeffRat 19 19 = (18 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 5 1 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_5 : ramanujanGcdClassWindowAverageRat X0 5 5 = (1001 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 19 1 = (4738 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_19 : ramanujanGcdClassWindowAverageRat X0 19 19 = (263 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 19 5 1 = (76 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 19 5 5 = (19 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 19 19 1 = (90 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_19 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 19 19 19 = (5 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 19 1 1 = (72 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_19 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 19 1 19 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 19 5 1 = (18 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_19 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 19 5 19 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_5, hCoeffRight_1, hCoeffRight_19, hAvgLeft_1, hAvgLeft_5, hAvgRight_1, hAvgRight_19, hBlockLeft_1, hBlockLeft_5, hBlockRight_1, hBlockRight_19, hPair_1_1, hPair_1_19, hPair_5_1, hPair_5_19]

theorem periodicMainPair_5_19_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 5 19) = (-30875 : ℚ) / 2025810081 := by
  have hneq : 5 ≠ 19 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 5 = (5 : ℚ) / 16 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 19 = (5 : ℚ) / 324 := by
    native_decide
  have hvalue : ((5 : ℚ) / 16) * ((5 : ℚ) / 324) * ((-79040 : ℚ) / 25010001) = (-30875 : ℚ) / 2025810081 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_5_19_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_5_22_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 5 22 = (8800 : ℚ) / 2778889 := by
  have hDivLeft : Nat.divisors 5 = ([1, 5] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 22 = ([1, 2, 11, 22] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 5 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_5 : ramanujanGcdClassCoeffRat 5 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 22 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2 : ramanujanGcdClassCoeffRat 22 2 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_11 : ramanujanGcdClassCoeffRat 22 11 = (-10 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_22 : ramanujanGcdClassCoeffRat 22 22 = (10 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 5 1 = (4000 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_5 : ramanujanGcdClassWindowAverageRat X0 5 5 = (1001 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 22 1 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_2 : ramanujanGcdClassWindowAverageRat X0 22 2 = (4546 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_11 : ramanujanGcdClassWindowAverageRat X0 22 11 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_22 : ramanujanGcdClassWindowAverageRat X0 22 22 = (455 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 22 5 1 = (88 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 22 5 5 = (22 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 22 22 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_2 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 22 22 2 = (100 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_11 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 22 22 11 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_22 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 5 22 22 22 = (10 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 22 1 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 22 1 2 = (80 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_11 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 22 1 11 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_22 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 22 1 22 = (8 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 22 5 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 22 5 2 = (20 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_11 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 22 5 11 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_5_22 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 5 22 5 22 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_5, hCoeffRight_1, hCoeffRight_2, hCoeffRight_11, hCoeffRight_22, hAvgLeft_1, hAvgLeft_5, hAvgRight_1, hAvgRight_2, hAvgRight_11, hAvgRight_22, hBlockLeft_1, hBlockLeft_5, hBlockRight_1, hBlockRight_2, hBlockRight_11, hBlockRight_22, hPair_1_1, hPair_1_2, hPair_1_11, hPair_1_22, hPair_5_1, hPair_5_2, hPair_5_11, hPair_5_22]

theorem periodicMainPair_5_22_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 5 22) = (275 : ℚ) / 5557778 := by
  have hneq : 5 ≠ 22 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 5 = (5 : ℚ) / 16 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 22 = (1 : ℚ) / 20 := by
    native_decide
  have hvalue : ((5 : ℚ) / 16) * ((1 : ℚ) / 20) * ((8800 : ℚ) / 2778889) = (275 : ℚ) / 5557778 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_5_22_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsBatch001Pairs : Finset (ℕ × ℕ) :=
  [(3, 6), (5, 7), (5, 10), (5, 11), (5, 13), (5, 14), (5, 15), (5, 17), (5, 19), (5, 22)].toFinset

noncomputable def PeriodicMainRecordsBatch001Value (p : ℕ × ℕ) : ℚ :=
  if p = (3, 6) then (62475 : ℚ) / 4 else
  if p = (5, 7) then (-62125 : ℚ) / 600240024 else
  if p = (5, 10) then (390781328125 : ℚ) / 200080008 else
  if p = (5, 11) then (275 : ℚ) / 5557778 else
  if p = (5, 13) then (30875 : ℚ) / 900360036 else
  if p = (5, 14) then (-62125 : ℚ) / 600240024 else
  if p = (5, 15) then (-69375 : ℚ) / 355697792 else
  if p = (5, 17) then (-61625 : ℚ) / 4268373504 else
  if p = (5, 19) then (-30875 : ℚ) / 2025810081 else
  if p = (5, 22) then (275 : ℚ) / 5557778 else
  0

def PeriodicMainRecordsBatch001Total : ℚ := (18225808151167625 : ℚ) / 1037214761472

theorem PeriodicMainRecordsBatch001_support_3_6 :
    (3, 6) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 3 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_5_7 :
    (5, 7) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 7 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 5 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 7 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_5_10 :
    (5, 10) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 5 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 10 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_5_11 :
    (5, 11) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 11 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 5 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 11 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_5_13 :
    (5, 13) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 13 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 5 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 13 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_5_14 :
    (5, 14) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 14 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 5 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 14 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_5_15 :
    (5, 15) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 15 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 5 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 15 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_5_17 :
    (5, 17) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 17 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 5 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 17 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_5_19 :
    (5, 19) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 19 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 5 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 19 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_5_22 :
    (5, 22) ∈ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  have hqCoeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hq2Coeff : 22 ∈ PeriodicMainCoeffSupportExplicit := by
    unfold PeriodicMainCoeffSupportExplicit
    exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
  have hqActive : 5 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
  have hq2Active : 22 ∈ PeriodicMainActiveSupportExplicit := by
    unfold PeriodicMainActiveSupportExplicit
    exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
  unfold PeriodicMainFullBlockOrderedPairSupportExplicit
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainActiveOrderedPairSupportExplicit
    exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
    by
      constructor
      · norm_num
      · norm_num [centeredRamanujanPairBlockPeriod, H]
  ⟩

theorem PeriodicMainRecordsBatch001_support_subset :
    PeriodicMainRecordsBatch001Pairs ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  intro p hp
  simp [PeriodicMainRecordsBatch001Pairs] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h
  · subst p
    exact PeriodicMainRecordsBatch001_support_3_6
  · subst p
    exact PeriodicMainRecordsBatch001_support_5_7
  · subst p
    exact PeriodicMainRecordsBatch001_support_5_10
  · subst p
    exact PeriodicMainRecordsBatch001_support_5_11
  · subst p
    exact PeriodicMainRecordsBatch001_support_5_13
  · subst p
    exact PeriodicMainRecordsBatch001_support_5_14
  · subst p
    exact PeriodicMainRecordsBatch001_support_5_15
  · subst p
    exact PeriodicMainRecordsBatch001_support_5_17
  · subst p
    exact PeriodicMainRecordsBatch001_support_5_19
  · subst p
    exact PeriodicMainRecordsBatch001_support_5_22

theorem PeriodicMainRecordsBatch001_value_on_records :
    ∀ p ∈ PeriodicMainRecordsBatch001Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = PeriodicMainRecordsBatch001Value p := by
  intro p hp
  simp [PeriodicMainRecordsBatch001Pairs] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_3_6_X1000000_orderedSummand]
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_5_7_X1000000_orderedSummand]
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_5_10_X1000000_orderedSummand]
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_5_11_X1000000_orderedSummand]
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_5_13_X1000000_orderedSummand]
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_5_14_X1000000_orderedSummand]
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_5_15_X1000000_orderedSummand]
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_5_17_X1000000_orderedSummand]
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_5_19_X1000000_orderedSummand]
  · subst p
    simp [PeriodicMainRecordsBatch001Value, periodicMainPair_5_22_X1000000_orderedSummand]

theorem PeriodicMainRecordsBatch001_records_sum :
    (∑ p ∈ PeriodicMainRecordsBatch001Pairs, PeriodicMainRecordsBatch001Value p) = PeriodicMainRecordsBatch001Total := by
  norm_num [PeriodicMainRecordsBatch001Pairs, PeriodicMainRecordsBatch001Value, PeriodicMainRecordsBatch001Total]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
