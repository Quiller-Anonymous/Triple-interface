import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

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

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
