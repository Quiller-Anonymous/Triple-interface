import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main zero-record proofs for selected JSON indices [0,5). -/

theorem periodicMainPair_21_7_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 21 7 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 21 = ([1, 3, 7, 21] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 7 = ([1, 7] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 21 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 21 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 21 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_21 : ramanujanGcdClassCoeffRat 21 21 = (12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 7 7 = (6 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 21 1 = (2858 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 21 3 = (1429 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 21 7 = (476 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_21 : ramanujanGcdClassWindowAverageRat X0 21 21 = (238 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 7 7 = (238 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 7 21 1 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 7 21 3 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 7 21 7 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 7 21 21 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 7 7 1 = (18 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 7 7 7 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 7 1 1 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 7 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 7 3 1 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 7 3 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 7 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 7 7 7 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 7 21 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 7 21 7 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  let T : ℕ → ℕ → ℚ := fun g h =>
    ramanujanGcdClassCoeffRat 21 g * ramanujanGcdClassCoeffRat 7 h
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 21 7) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 7 g h
              - ramanujanGcdClassWindowAverageRat X0 7 h
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 7 21 g
              - ramanujanGcdClassWindowAverageRat X0 21 g
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 7 7 h
              + ramanujanGcdClassWindowAverageRat X0 21 g
                  * ramanujanGcdClassWindowAverageRat X0 7 h
                  * evenRamanujanBlockCountRat 21 7))
  have hTerm_1_1 :
      T 1 1 = (-1133786780 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_1, hAvgLeft_1, hAvgRight_1, hBlockLeft_1, hBlockRight_1, hPair_1_1]
  have hTerm_1_7 :
      T 1 7 = (-6802720680 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_7, hAvgLeft_1, hAvgRight_7, hBlockLeft_1, hBlockRight_7, hPair_1_7]
  have hTerm_3_1 :
      T 3 1 = (1133786780 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_1, hAvgLeft_3, hAvgRight_1, hBlockLeft_3, hBlockRight_1, hPair_3_1]
  have hTerm_3_7 :
      T 3 7 = (6802720680 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_7, hAvgLeft_3, hAvgRight_7, hBlockLeft_3, hBlockRight_7, hPair_3_7]
  have hTerm_7_1 :
      T 7 1 = (-6802720680 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_1, hAvgLeft_7, hAvgRight_1, hBlockLeft_7, hBlockRight_1, hPair_7_1]
  have hTerm_7_7 :
      T 7 7 = (-40816324080 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_7, hAvgLeft_7, hAvgRight_7, hBlockLeft_7, hBlockRight_7, hPair_7_7]
  have hTerm_21_1 :
      T 21 1 = (6802720680 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_1, hAvgLeft_21, hAvgRight_1, hBlockLeft_21, hBlockRight_1, hPair_21_1]
  have hTerm_21_7 :
      T 21 7 = (40816324080 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_7, hAvgLeft_21, hAvgRight_7, hBlockLeft_21, hBlockRight_7, hPair_21_7]
  have hRow_1 :
      (∑ h ∈ Nat.divisors 7, T 1 h) = (-7936507460 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_1_1, hTerm_1_7]
  have hRow_3 :
      (∑ h ∈ Nat.divisors 7, T 3 h) = (7936507460 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_3_1, hTerm_3_7]
  have hRow_7 :
      (∑ h ∈ Nat.divisors 7, T 7 h) = (-47619044760 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_7_1, hTerm_7_7]
  have hRow_21 :
      (∑ h ∈ Nat.divisors 7, T 21 h) = (47619044760 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_21_1, hTerm_21_7]
  unfold centeredRamanujanPairPeriodicMainTermRat
  change (∑ g ∈ Nat.divisors 21, ∑ h ∈ Nat.divisors 7, T g h) = (0 : ℚ) / 1
  norm_num [hDivLeft, hDivRight, hTerm_1_1, hTerm_1_7, hTerm_3_1, hTerm_3_7, hTerm_7_1, hTerm_7_7, hTerm_21_1, hTerm_21_7]

theorem periodicMainPair_21_7_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 21 7) = (0 : ℚ) / 1 := by
  have hneq : 21 ≠ 7 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 21 = (5 : ℚ) / 144 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 7 = (5 : ℚ) / 36 := by
    native_decide
  have hvalue : ((5 : ℚ) / 144) * ((5 : ℚ) / 36) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_21_7_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_21_14_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 21 14 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 21 = ([1, 3, 7, 21] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 14 = ([1, 2, 7, 14] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 21 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 21 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 21 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_21 : ramanujanGcdClassCoeffRat 21 21 = (12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 14 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2 : ramanujanGcdClassCoeffRat 14 2 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 14 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_14 : ramanujanGcdClassCoeffRat 14 14 = (6 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 21 1 = (2858 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 21 3 = (1429 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 21 7 = (476 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_21 : ramanujanGcdClassWindowAverageRat X0 21 21 = (238 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 14 1 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_2 : ramanujanGcdClassWindowAverageRat X0 14 2 = (1429 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 14 7 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_14 : ramanujanGcdClassWindowAverageRat X0 14 14 = (238 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 21 1 = (24 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 21 3 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 21 7 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 21 21 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 14 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_2 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 14 2 = (36 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 14 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_14 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 14 14 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 1 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 1 2 = (24 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 1 14 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 3 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 3 2 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 3 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 3 14 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 7 2 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 7 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 7 14 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 21 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 21 2 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 21 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 21 14 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  let T : ℕ → ℕ → ℚ := fun g h =>
    ramanujanGcdClassCoeffRat 21 g * ramanujanGcdClassCoeffRat 14 h
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 21 14) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 14 g h
              - ramanujanGcdClassWindowAverageRat X0 14 h
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 21 g
              - ramanujanGcdClassWindowAverageRat X0 21 g
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 14 14 h
              + ramanujanGcdClassWindowAverageRat X0 21 g
                  * ramanujanGcdClassWindowAverageRat X0 14 h
                  * evenRamanujanBlockCountRat 21 14))
  have hTerm_1_1 :
      T 1 1 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_1, hAvgLeft_1, hAvgRight_1, hBlockLeft_1, hBlockRight_1, hPair_1_1]
  have hTerm_1_2 :
      T 1 2 = (-1133786780 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_2, hAvgLeft_1, hAvgRight_2, hBlockLeft_1, hBlockRight_2, hPair_1_2]
  have hTerm_1_7 :
      T 1 7 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_7, hAvgLeft_1, hAvgRight_7, hBlockLeft_1, hBlockRight_7, hPair_1_7]
  have hTerm_1_14 :
      T 1 14 = (-6802720680 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_14, hAvgLeft_1, hAvgRight_14, hBlockLeft_1, hBlockRight_14, hPair_1_14]
  have hTerm_3_1 :
      T 3 1 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_1, hAvgLeft_3, hAvgRight_1, hBlockLeft_3, hBlockRight_1, hPair_3_1]
  have hTerm_3_2 :
      T 3 2 = (1133786780 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_2, hAvgLeft_3, hAvgRight_2, hBlockLeft_3, hBlockRight_2, hPair_3_2]
  have hTerm_3_7 :
      T 3 7 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_7, hAvgLeft_3, hAvgRight_7, hBlockLeft_3, hBlockRight_7, hPair_3_7]
  have hTerm_3_14 :
      T 3 14 = (6802720680 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_14, hAvgLeft_3, hAvgRight_14, hBlockLeft_3, hBlockRight_14, hPair_3_14]
  have hTerm_7_1 :
      T 7 1 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_1, hAvgLeft_7, hAvgRight_1, hBlockLeft_7, hBlockRight_1, hPair_7_1]
  have hTerm_7_2 :
      T 7 2 = (-6802720680 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_2, hAvgLeft_7, hAvgRight_2, hBlockLeft_7, hBlockRight_2, hPair_7_2]
  have hTerm_7_7 :
      T 7 7 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_7, hAvgLeft_7, hAvgRight_7, hBlockLeft_7, hBlockRight_7, hPair_7_7]
  have hTerm_7_14 :
      T 7 14 = (-40816324080 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_14, hAvgLeft_7, hAvgRight_14, hBlockLeft_7, hBlockRight_14, hPair_7_14]
  have hTerm_21_1 :
      T 21 1 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_1, hAvgLeft_21, hAvgRight_1, hBlockLeft_21, hBlockRight_1, hPair_21_1]
  have hTerm_21_2 :
      T 21 2 = (6802720680 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_2, hAvgLeft_21, hAvgRight_2, hBlockLeft_21, hBlockRight_2, hPair_21_2]
  have hTerm_21_7 :
      T 21 7 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_7, hAvgLeft_21, hAvgRight_7, hBlockLeft_21, hBlockRight_7, hPair_21_7]
  have hTerm_21_14 :
      T 21 14 = (40816324080 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_14, hAvgLeft_21, hAvgRight_14, hBlockLeft_21, hBlockRight_14, hPair_21_14]
  have hRow_1 :
      (∑ h ∈ Nat.divisors 14, T 1 h) = (-7936507460 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_1_1, hTerm_1_2, hTerm_1_7, hTerm_1_14]
  have hRow_3 :
      (∑ h ∈ Nat.divisors 14, T 3 h) = (7936507460 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_3_1, hTerm_3_2, hTerm_3_7, hTerm_3_14]
  have hRow_7 :
      (∑ h ∈ Nat.divisors 14, T 7 h) = (-47619044760 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_7_1, hTerm_7_2, hTerm_7_7, hTerm_7_14]
  have hRow_21 :
      (∑ h ∈ Nat.divisors 14, T 21 h) = (47619044760 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_21_1, hTerm_21_2, hTerm_21_7, hTerm_21_14]
  unfold centeredRamanujanPairPeriodicMainTermRat
  change (∑ g ∈ Nat.divisors 21, ∑ h ∈ Nat.divisors 14, T g h) = (0 : ℚ) / 1
  norm_num [hDivLeft, hDivRight, hTerm_1_1, hTerm_1_2, hTerm_1_7, hTerm_1_14, hTerm_3_1, hTerm_3_2, hTerm_3_7, hTerm_3_14, hTerm_7_1, hTerm_7_2, hTerm_7_7, hTerm_7_14, hTerm_21_1, hTerm_21_2, hTerm_21_7, hTerm_21_14]

theorem periodicMainPair_21_14_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 21 14) = (0 : ℚ) / 1 := by
  have hneq : 21 ≠ 14 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 21 = (5 : ℚ) / 144 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 14 = (5 : ℚ) / 36 := by
    native_decide
  have hvalue : ((5 : ℚ) / 144) * ((5 : ℚ) / 36) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_21_14_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_21_35_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 21 35 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 21 = ([1, 3, 7, 21] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 35 = ([1, 5, 7, 35] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 21 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 21 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 21 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_21 : ramanujanGcdClassCoeffRat 21 21 = (12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 35 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_5 : ramanujanGcdClassCoeffRat 35 5 = (-4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 35 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_35 : ramanujanGcdClassCoeffRat 35 35 = (24 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 21 1 = (2858 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 21 3 = (1429 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 21 7 = (476 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_21 : ramanujanGcdClassWindowAverageRat X0 21 21 = (238 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 35 1 = (1143 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_5 : ramanujanGcdClassWindowAverageRat X0 35 5 = (286 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 35 7 = (571 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_35 : ramanujanGcdClassWindowAverageRat X0 35 35 = (143 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 21 1 = (60 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 21 3 = (30 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 21 7 = (10 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 21 21 = (5 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 35 1 = (72 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 35 5 = (18 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 35 7 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_35 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 35 35 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 1 1 = (48 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 1 5 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_35 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 1 35 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 3 1 = (24 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 3 5 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 3 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_35 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 3 35 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 7 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 7 7 = (8 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_35 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 7 35 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 21 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 21 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 21 7 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_35 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 21 35 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  let T : ℕ → ℕ → ℚ := fun g h =>
    ramanujanGcdClassCoeffRat 21 g * ramanujanGcdClassCoeffRat 35 h
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 21 35) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 35 g h
              - ramanujanGcdClassWindowAverageRat X0 35 h
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 21 g
              - ramanujanGcdClassWindowAverageRat X0 21 g
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 35 35 h
              + ramanujanGcdClassWindowAverageRat X0 21 g
                  * ramanujanGcdClassWindowAverageRat X0 35 h
                  * evenRamanujanBlockCountRat 21 35))
  have hTerm_1_1 :
      T 1 1 = (895596186 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_1, hAvgLeft_1, hAvgRight_1, hBlockLeft_1, hBlockRight_1, hPair_1_1]
  have hTerm_1_5 :
      T 1 5 = (-895596656 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_5, hAvgLeft_1, hAvgRight_5, hBlockLeft_1, hBlockRight_5, hPair_1_5]
  have hTerm_1_7 :
      T 1 7 = (5373577868 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_7, hAvgLeft_1, hAvgRight_7, hBlockLeft_1, hBlockRight_7, hPair_1_7]
  have hTerm_1_35 :
      T 1 35 = (-5373576928 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_35, hAvgLeft_1, hAvgRight_35, hBlockLeft_1, hBlockRight_35, hPair_1_35]
  have hTerm_3_1 :
      T 3 1 = (-895596186 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_1, hAvgLeft_3, hAvgRight_1, hBlockLeft_3, hBlockRight_1, hPair_3_1]
  have hTerm_3_5 :
      T 3 5 = (895596656 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_5, hAvgLeft_3, hAvgRight_5, hBlockLeft_3, hBlockRight_5, hPair_3_5]
  have hTerm_3_7 :
      T 3 7 = (-5373577868 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_7, hAvgLeft_3, hAvgRight_7, hBlockLeft_3, hBlockRight_7, hPair_3_7]
  have hTerm_3_35 :
      T 3 35 = (5373576928 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_35, hAvgLeft_3, hAvgRight_35, hBlockLeft_3, hBlockRight_35, hPair_3_35]
  have hTerm_7_1 :
      T 7 1 = (5373577116 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_1, hAvgLeft_7, hAvgRight_1, hBlockLeft_7, hBlockRight_1, hPair_7_1]
  have hTerm_7_5 :
      T 7 5 = (-5373579936 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_5, hAvgLeft_7, hAvgRight_5, hBlockLeft_7, hBlockRight_5, hPair_7_5]
  have hTerm_7_7 :
      T 7 7 = (32241467208 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_7, hAvgLeft_7, hAvgRight_7, hBlockLeft_7, hBlockRight_7, hPair_7_7]
  have hTerm_7_35 :
      T 7 35 = (-32241461568 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_35, hAvgLeft_7, hAvgRight_35, hBlockLeft_7, hBlockRight_35, hPair_7_35]
  have hTerm_21_1 :
      T 21 1 = (-5373577116 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_1, hAvgLeft_21, hAvgRight_1, hBlockLeft_21, hBlockRight_1, hPair_21_1]
  have hTerm_21_5 :
      T 21 5 = (5373579936 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_5, hAvgLeft_21, hAvgRight_5, hBlockLeft_21, hBlockRight_5, hPair_21_5]
  have hTerm_21_7 :
      T 21 7 = (-32241467208 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_7, hAvgLeft_21, hAvgRight_7, hBlockLeft_21, hBlockRight_7, hPair_21_7]
  have hTerm_21_35 :
      T 21 35 = (32241461568 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_35, hAvgLeft_21, hAvgRight_35, hBlockLeft_21, hBlockRight_35, hPair_21_35]
  have hRow_1 :
      (∑ h ∈ Nat.divisors 35, T 1 h) = (470 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_1_1, hTerm_1_5, hTerm_1_7, hTerm_1_35]
  have hRow_3 :
      (∑ h ∈ Nat.divisors 35, T 3 h) = (-470 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_3_1, hTerm_3_5, hTerm_3_7, hTerm_3_35]
  have hRow_7 :
      (∑ h ∈ Nat.divisors 35, T 7 h) = (2820 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_7_1, hTerm_7_5, hTerm_7_7, hTerm_7_35]
  have hRow_21 :
      (∑ h ∈ Nat.divisors 35, T 21 h) = (-2820 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_21_1, hTerm_21_5, hTerm_21_7, hTerm_21_35]
  unfold centeredRamanujanPairPeriodicMainTermRat
  change (∑ g ∈ Nat.divisors 21, ∑ h ∈ Nat.divisors 35, T g h) = (0 : ℚ) / 1
  norm_num [hDivLeft, hDivRight, hTerm_1_1, hTerm_1_5, hTerm_1_7, hTerm_1_35, hTerm_3_1, hTerm_3_5, hTerm_3_7, hTerm_3_35, hTerm_7_1, hTerm_7_5, hTerm_7_7, hTerm_7_35, hTerm_21_1, hTerm_21_5, hTerm_21_7, hTerm_21_35]

theorem periodicMainPair_21_35_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 21 35) = (0 : ℚ) / 1 := by
  have hneq : 21 ≠ 35 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 21 = (5 : ℚ) / 144 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 35 = (5 : ℚ) / 576 := by
    native_decide
  have hvalue : ((5 : ℚ) / 144) * ((5 : ℚ) / 576) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_21_35_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_21_70_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 21 70 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 21 = ([1, 3, 7, 21] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 70 = ([1, 2, 5, 7, 10, 14, 35, 70] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 21 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 21 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 21 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_21 : ramanujanGcdClassCoeffRat 21 21 = (12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 70 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2 : ramanujanGcdClassCoeffRat 70 2 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_5 : ramanujanGcdClassCoeffRat 70 5 = (4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 70 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_10 : ramanujanGcdClassCoeffRat 70 10 = (-4 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_14 : ramanujanGcdClassCoeffRat 70 14 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_35 : ramanujanGcdClassCoeffRat 70 35 = (-24 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_70 : ramanujanGcdClassCoeffRat 70 70 = (24 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 21 1 = (2858 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 21 3 = (1429 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 21 7 = (476 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_21 : ramanujanGcdClassWindowAverageRat X0 21 21 = (238 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 70 1 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_2 : ramanujanGcdClassWindowAverageRat X0 70 2 = (1143 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_5 : ramanujanGcdClassWindowAverageRat X0 70 5 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 70 7 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_10 : ramanujanGcdClassWindowAverageRat X0 70 10 = (286 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_14 : ramanujanGcdClassWindowAverageRat X0 70 14 = (571 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_35 : ramanujanGcdClassWindowAverageRat X0 70 35 = (0 : ℚ) / 1 := by
    native_decide
  have hAvgRight_70 : ramanujanGcdClassWindowAverageRat X0 70 70 = (143 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 21 1 = (120 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 21 3 = (60 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 21 7 = (20 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 21 21 = (10 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 70 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_2 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 70 2 = (144 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 70 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 70 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_10 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 70 10 = (36 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_14 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 70 14 = (24 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_35 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 70 35 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
    · norm_num [Goldbach.Windows.IsEven]
    · norm_num [Goldbach.Windows.IsEven]
  have hBlockRight_70 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 70 70 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 1 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 1 2 = (96 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 1 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_10 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 1 10 = (24 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 1 14 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_35 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 1 35 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_70 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 1 70 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 3 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 3 2 = (48 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 3 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 3 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_10 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 3 10 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 3 14 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_35 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 3 35 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_70 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 3 70 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 7 2 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 7 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 7 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_10 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 7 10 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 7 14 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_35 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 7 35 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_70 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 7 70 = (4 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 21 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_2 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 21 2 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_5 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 21 5 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 21 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_10 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 21 10 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_14 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 21 14 = (8 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_35 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 21 35 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus]
      · norm_num [Goldbach.Windows.IsEven]
      · norm_num [Goldbach.Windows.IsEven, ramanujanGcdClassJointModulus]
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_70 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 21 70 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_even_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  let T : ℕ → ℕ → ℚ := fun g h =>
    ramanujanGcdClassCoeffRat 21 g * ramanujanGcdClassCoeffRat 70 h
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 21 70) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 70 g h
              - ramanujanGcdClassWindowAverageRat X0 70 h
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 21 g
              - ramanujanGcdClassWindowAverageRat X0 21 g
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 70 70 h
              + ramanujanGcdClassWindowAverageRat X0 21 g
                  * ramanujanGcdClassWindowAverageRat X0 70 h
                  * evenRamanujanBlockCountRat 21 70))
  have hTerm_1_1 :
      T 1 1 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_1, hAvgLeft_1, hAvgRight_1, hBlockLeft_1, hBlockRight_1, hPair_1_1]
  have hTerm_1_2 :
      T 1 2 = (876540948 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_2, hAvgLeft_1, hAvgRight_2, hBlockLeft_1, hBlockRight_2, hPair_1_2]
  have hTerm_1_5 :
      T 1 5 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_5, hAvgLeft_1, hAvgRight_5, hBlockLeft_1, hBlockRight_5, hPair_1_5]
  have hTerm_1_7 :
      T 1 7 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_7, hAvgLeft_1, hAvgRight_7, hBlockLeft_1, hBlockRight_7, hPair_1_7]
  have hTerm_1_10 :
      T 1 10 = (-876541408 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_10, hAvgLeft_1, hAvgRight_10, hBlockLeft_1, hBlockRight_10, hPair_1_10]
  have hTerm_1_14 :
      T 1 14 = (5259246424 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_14, hAvgLeft_1, hAvgRight_14, hBlockLeft_1, hBlockRight_14, hPair_1_14]
  have hTerm_1_35 :
      T 1 35 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_35, hAvgLeft_1, hAvgRight_35, hBlockLeft_1, hBlockRight_35, hPair_1_35]
  have hTerm_1_70 :
      T 1 70 = (-5259245504 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_70, hAvgLeft_1, hAvgRight_70, hBlockLeft_1, hBlockRight_70, hPair_1_70]
  have hTerm_3_1 :
      T 3 1 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_1, hAvgLeft_3, hAvgRight_1, hBlockLeft_3, hBlockRight_1, hPair_3_1]
  have hTerm_3_2 :
      T 3 2 = (-876540948 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_2, hAvgLeft_3, hAvgRight_2, hBlockLeft_3, hBlockRight_2, hPair_3_2]
  have hTerm_3_5 :
      T 3 5 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_5, hAvgLeft_3, hAvgRight_5, hBlockLeft_3, hBlockRight_5, hPair_3_5]
  have hTerm_3_7 :
      T 3 7 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_7, hAvgLeft_3, hAvgRight_7, hBlockLeft_3, hBlockRight_7, hPair_3_7]
  have hTerm_3_10 :
      T 3 10 = (876541408 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_10, hAvgLeft_3, hAvgRight_10, hBlockLeft_3, hBlockRight_10, hPair_3_10]
  have hTerm_3_14 :
      T 3 14 = (-5259246424 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_14, hAvgLeft_3, hAvgRight_14, hBlockLeft_3, hBlockRight_14, hPair_3_14]
  have hTerm_3_35 :
      T 3 35 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_35, hAvgLeft_3, hAvgRight_35, hBlockLeft_3, hBlockRight_35, hPair_3_35]
  have hTerm_3_70 :
      T 3 70 = (5259245504 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_70, hAvgLeft_3, hAvgRight_70, hBlockLeft_3, hBlockRight_70, hPair_3_70]
  have hTerm_7_1 :
      T 7 1 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_1, hAvgLeft_7, hAvgRight_1, hBlockLeft_7, hBlockRight_1, hPair_7_1]
  have hTerm_7_2 :
      T 7 2 = (5259245688 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_2, hAvgLeft_7, hAvgRight_2, hBlockLeft_7, hBlockRight_2, hPair_7_2]
  have hTerm_7_5 :
      T 7 5 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_5, hAvgLeft_7, hAvgRight_5, hBlockLeft_7, hBlockRight_5, hPair_7_5]
  have hTerm_7_7 :
      T 7 7 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_7, hAvgLeft_7, hAvgRight_7, hBlockLeft_7, hBlockRight_7, hPair_7_7]
  have hTerm_7_10 :
      T 7 10 = (-5259248448 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_10, hAvgLeft_7, hAvgRight_10, hBlockLeft_7, hBlockRight_10, hPair_7_10]
  have hTerm_7_14 :
      T 7 14 = (31555478544 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_14, hAvgLeft_7, hAvgRight_14, hBlockLeft_7, hBlockRight_14, hPair_7_14]
  have hTerm_7_35 :
      T 7 35 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_35, hAvgLeft_7, hAvgRight_35, hBlockLeft_7, hBlockRight_35, hPair_7_35]
  have hTerm_7_70 :
      T 7 70 = (-31555473024 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_70, hAvgLeft_7, hAvgRight_70, hBlockLeft_7, hBlockRight_70, hPair_7_70]
  have hTerm_21_1 :
      T 21 1 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_1, hAvgLeft_21, hAvgRight_1, hBlockLeft_21, hBlockRight_1, hPair_21_1]
  have hTerm_21_2 :
      T 21 2 = (-5259245688 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_2, hAvgLeft_21, hAvgRight_2, hBlockLeft_21, hBlockRight_2, hPair_21_2]
  have hTerm_21_5 :
      T 21 5 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_5, hAvgLeft_21, hAvgRight_5, hBlockLeft_21, hBlockRight_5, hPair_21_5]
  have hTerm_21_7 :
      T 21 7 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_7, hAvgLeft_21, hAvgRight_7, hBlockLeft_21, hBlockRight_7, hPair_21_7]
  have hTerm_21_10 :
      T 21 10 = (5259248448 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_10, hAvgLeft_21, hAvgRight_10, hBlockLeft_21, hBlockRight_10, hPair_21_10]
  have hTerm_21_14 :
      T 21 14 = (-31555478544 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_14, hAvgLeft_21, hAvgRight_14, hBlockLeft_21, hBlockRight_14, hPair_21_14]
  have hTerm_21_35 :
      T 21 35 = (0 : ℚ) / 1 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_35, hAvgLeft_21, hAvgRight_35, hBlockLeft_21, hBlockRight_35, hPair_21_35]
  have hTerm_21_70 :
      T 21 70 = (31555473024 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_70, hAvgLeft_21, hAvgRight_70, hBlockLeft_21, hBlockRight_70, hPair_21_70]
  have hRow_1 :
      (∑ h ∈ Nat.divisors 70, T 1 h) = (460 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_1_1, hTerm_1_2, hTerm_1_5, hTerm_1_7, hTerm_1_10, hTerm_1_14, hTerm_1_35, hTerm_1_70]
  have hRow_3 :
      (∑ h ∈ Nat.divisors 70, T 3 h) = (-460 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_3_1, hTerm_3_2, hTerm_3_5, hTerm_3_7, hTerm_3_10, hTerm_3_14, hTerm_3_35, hTerm_3_70]
  have hRow_7 :
      (∑ h ∈ Nat.divisors 70, T 7 h) = (2760 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_7_1, hTerm_7_2, hTerm_7_5, hTerm_7_7, hTerm_7_10, hTerm_7_14, hTerm_7_35, hTerm_7_70]
  have hRow_21 :
      (∑ h ∈ Nat.divisors 70, T 21 h) = (-2760 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_21_1, hTerm_21_2, hTerm_21_5, hTerm_21_7, hTerm_21_10, hTerm_21_14, hTerm_21_35, hTerm_21_70]
  unfold centeredRamanujanPairPeriodicMainTermRat
  change (∑ g ∈ Nat.divisors 21, ∑ h ∈ Nat.divisors 70, T g h) = (0 : ℚ) / 1
  norm_num [hDivLeft, hDivRight, hTerm_1_1, hTerm_1_2, hTerm_1_5, hTerm_1_7, hTerm_1_10, hTerm_1_14, hTerm_1_35, hTerm_1_70, hTerm_3_1, hTerm_3_2, hTerm_3_5, hTerm_3_7, hTerm_3_10, hTerm_3_14, hTerm_3_35, hTerm_3_70, hTerm_7_1, hTerm_7_2, hTerm_7_5, hTerm_7_7, hTerm_7_10, hTerm_7_14, hTerm_7_35, hTerm_7_70, hTerm_21_1, hTerm_21_2, hTerm_21_5, hTerm_21_7, hTerm_21_10, hTerm_21_14, hTerm_21_35, hTerm_21_70]

theorem periodicMainPair_21_70_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 21 70) = (0 : ℚ) / 1 := by
  have hneq : 21 ≠ 70 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 21 = (5 : ℚ) / 144 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 70 = (5 : ℚ) / 576 := by
    native_decide
  have hvalue : ((5 : ℚ) / 144) * ((5 : ℚ) / 576) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_21_70_X1000000_centeredTerm
    hvalue

theorem periodicMainPair_21_77_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 21 77 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 21 = ([1, 3, 7, 21] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 77 = ([1, 7, 11, 77] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 21 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 21 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 21 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_21 : ramanujanGcdClassCoeffRat 21 21 = (12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 77 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 77 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_11 : ramanujanGcdClassCoeffRat 77 11 = (-10 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_77 : ramanujanGcdClassCoeffRat 77 77 = (60 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 21 1 = (2858 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 21 3 = (1429 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 21 7 = (476 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_21 : ramanujanGcdClassWindowAverageRat X0 21 21 = (238 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 77 1 = (1299 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 77 7 = (649 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_11 : ramanujanGcdClassWindowAverageRat X0 77 11 = (130 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_77 : ramanujanGcdClassWindowAverageRat X0 77 77 = (65 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 21 1 = (132 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 21 3 = (66 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 21 7 = (22 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 21 21 = (11 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 77 1 = (180 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 77 7 = (30 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_11 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 77 11 = (18 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_77 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 77 77 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 1 1 = (120 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_11 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 1 11 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_77 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 1 77 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 3 1 = (60 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 3 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_11 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 3 11 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_77 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 3 77 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 7 7 = (20 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_11 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 7 11 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_77 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 7 77 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 21 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 21 7 = (10 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_11 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 21 11 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_77 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 21 77 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  let T : ℕ → ℕ → ℚ := fun g h =>
    ramanujanGcdClassCoeffRat 21 g * ramanujanGcdClassCoeffRat 77 h
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 21 77) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 21 77 g h
              - ramanujanGcdClassWindowAverageRat X0 77 h
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 21 g
              - ramanujanGcdClassWindowAverageRat X0 21 g
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 21 77 77 h
              + ramanujanGcdClassWindowAverageRat X0 21 g
                  * ramanujanGcdClassWindowAverageRat X0 77 h
                  * evenRamanujanBlockCountRat 21 77))
  have hTerm_1_1 :
      T 1 1 = (1000400058 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_1, hAvgLeft_1, hAvgRight_1, hBlockLeft_1, hBlockRight_1, hPair_1_1]
  have hTerm_1_7 :
      T 1 7 = (6002400684 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_7, hAvgLeft_1, hAvgRight_7, hBlockLeft_1, hBlockRight_7, hPair_1_7]
  have hTerm_1_11 :
      T 1 11 = (-1000400520 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_11, hAvgLeft_1, hAvgRight_11, hBlockLeft_1, hBlockRight_11, hPair_1_11]
  have hTerm_1_77 :
      T 1 77 = (-6002399760 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_1, hCoeffRight_77, hAvgLeft_1, hAvgRight_77, hBlockLeft_1, hBlockRight_77, hPair_1_77]
  have hTerm_3_1 :
      T 3 1 = (-1000400058 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_1, hAvgLeft_3, hAvgRight_1, hBlockLeft_3, hBlockRight_1, hPair_3_1]
  have hTerm_3_7 :
      T 3 7 = (-6002400684 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_7, hAvgLeft_3, hAvgRight_7, hBlockLeft_3, hBlockRight_7, hPair_3_7]
  have hTerm_3_11 :
      T 3 11 = (1000400520 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_11, hAvgLeft_3, hAvgRight_11, hBlockLeft_3, hBlockRight_11, hPair_3_11]
  have hTerm_3_77 :
      T 3 77 = (6002399760 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_3, hCoeffRight_77, hAvgLeft_3, hAvgRight_77, hBlockLeft_3, hBlockRight_77, hPair_3_77]
  have hTerm_7_1 :
      T 7 1 = (6002400348 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_1, hAvgLeft_7, hAvgRight_1, hBlockLeft_7, hBlockRight_1, hPair_7_1]
  have hTerm_7_7 :
      T 7 7 = (36014404104 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_7, hAvgLeft_7, hAvgRight_7, hBlockLeft_7, hBlockRight_7, hPair_7_7]
  have hTerm_7_11 :
      T 7 11 = (-6002403120 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_11, hAvgLeft_7, hAvgRight_11, hBlockLeft_7, hBlockRight_11, hPair_7_11]
  have hTerm_7_77 :
      T 7 77 = (-36014398560 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_7, hCoeffRight_77, hAvgLeft_7, hAvgRight_77, hBlockLeft_7, hBlockRight_77, hPair_7_77]
  have hTerm_21_1 :
      T 21 1 = (-6002400348 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_1, hAvgLeft_21, hAvgRight_1, hBlockLeft_21, hBlockRight_1, hPair_21_1]
  have hTerm_21_7 :
      T 21 7 = (-36014404104 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_7, hAvgLeft_21, hAvgRight_7, hBlockLeft_21, hBlockRight_7, hPair_21_7]
  have hTerm_21_11 :
      T 21 11 = (6002403120 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_11, hAvgLeft_21, hAvgRight_11, hBlockLeft_21, hBlockRight_11, hPair_21_11]
  have hTerm_21_77 :
      T 21 77 = (36014398560 : ℚ) / 2778889 := by
    dsimp [T]
    norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
      hCoeffLeft_21, hCoeffRight_77, hAvgLeft_21, hAvgRight_77, hBlockLeft_21, hBlockRight_77, hPair_21_77]
  have hRow_1 :
      (∑ h ∈ Nat.divisors 77, T 1 h) = (462 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_1_1, hTerm_1_7, hTerm_1_11, hTerm_1_77]
  have hRow_3 :
      (∑ h ∈ Nat.divisors 77, T 3 h) = (-462 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_3_1, hTerm_3_7, hTerm_3_11, hTerm_3_77]
  have hRow_7 :
      (∑ h ∈ Nat.divisors 77, T 7 h) = (2772 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_7_1, hTerm_7_7, hTerm_7_11, hTerm_7_77]
  have hRow_21 :
      (∑ h ∈ Nat.divisors 77, T 21 h) = (-2772 : ℚ) / 2778889 := by
    norm_num [hDivRight, hTerm_21_1, hTerm_21_7, hTerm_21_11, hTerm_21_77]
  unfold centeredRamanujanPairPeriodicMainTermRat
  change (∑ g ∈ Nat.divisors 21, ∑ h ∈ Nat.divisors 77, T g h) = (0 : ℚ) / 1
  norm_num [hDivLeft, hDivRight, hTerm_1_1, hTerm_1_7, hTerm_1_11, hTerm_1_77, hTerm_3_1, hTerm_3_7, hTerm_3_11, hTerm_3_77, hTerm_7_1, hTerm_7_7, hTerm_7_11, hTerm_7_77, hTerm_21_1, hTerm_21_7, hTerm_21_11, hTerm_21_77]

theorem periodicMainPair_21_77_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 21 77) = (0 : ℚ) / 1 := by
  have hneq : 21 ≠ 77 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 21 = (5 : ℚ) / 144 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 77 = (1 : ℚ) / 720 := by
    native_decide
  have hvalue : ((5 : ℚ) / 144) * ((1 : ℚ) / 720) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_21_77_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsPeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeDirect000Pairs : Finset (ℕ × ℕ) :=
  [(21, 7), (21, 14), (21, 35), (21, 70), (21, 77)].toFinset

theorem PeriodicMainRecordsPeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeDirect000_value_on_records :
    ∀ p ∈ PeriodicMainRecordsPeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeDirect000Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsPeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeDirect000Pairs] at hp
  rcases hp with h | h | h | h | h
  · subst p
    simpa using periodicMainPair_21_7_X1000000_orderedSummand
  · subst p
    simpa using periodicMainPair_21_14_X1000000_orderedSummand
  · subst p
    simpa using periodicMainPair_21_35_X1000000_orderedSummand
  · subst p
    simpa using periodicMainPair_21_70_X1000000_orderedSummand
  · subst p
    simpa using periodicMainPair_21_77_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
