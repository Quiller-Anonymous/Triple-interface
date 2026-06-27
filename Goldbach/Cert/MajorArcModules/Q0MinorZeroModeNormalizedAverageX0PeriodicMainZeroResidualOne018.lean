import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [18,19). -/

theorem periodicMainPair_889_2667_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 889 2667 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 889 = ([1, 7, 127, 889] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 2667 = ([1, 3, 7, 21, 127, 381, 889, 2667] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 889 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 889 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_127 : ramanujanGcdClassCoeffRat 889 127 = (-126 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_889 : ramanujanGcdClassCoeffRat 889 889 = (756 : ℚ) / 1 := by
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
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 889 1 = (1418 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 889 7 = (236 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_127 : ramanujanGcdClassWindowAverageRat X0 889 127 = (11 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_889 : ramanujanGcdClassWindowAverageRat X0 889 889 = (2 : ℚ) / 1667 := by
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
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 889 1 = (2268 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 889 7 = (378 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_127 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 889 127 = (18 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_889 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 889 889 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 2667 1 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 2667 3 = (756 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 2667 7 = (252 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 2667 21 = (126 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_127 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 2667 127 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_381 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 2667 381 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_889 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 2667 889 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_2667 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 889 2667 2667 2667 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 1 1 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 1 3 = (756 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 1 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 1 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_381 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 1 381 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 1 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2667 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 1 2667 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 7 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 7 7 = (252 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 7 21 = (126 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 7 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_381 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 7 381 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 7 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_2667 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 7 2667 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 127 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 127 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 127 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 127 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 127 127 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_381 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 127 381 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 127 889 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_127_2667 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 127 2667 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 889 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 889 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 889 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 889 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_127 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 889 127 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_381 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 889 381 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_889 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 889 889 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_889_2667 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 889 2667 889 2667 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_7, hCoeffLeft_127, hCoeffLeft_889, hCoeffRight_1, hCoeffRight_3, hCoeffRight_7, hCoeffRight_21, hCoeffRight_127, hCoeffRight_381, hCoeffRight_889, hCoeffRight_2667, hAvgLeft_1, hAvgLeft_7, hAvgLeft_127, hAvgLeft_889, hAvgRight_1, hAvgRight_3, hAvgRight_7, hAvgRight_21, hAvgRight_127, hAvgRight_381, hAvgRight_889, hAvgRight_2667, hBlockLeft_1, hBlockLeft_7, hBlockLeft_127, hBlockLeft_889, hBlockRight_1, hBlockRight_3, hBlockRight_7, hBlockRight_21, hBlockRight_127, hBlockRight_381, hBlockRight_889, hBlockRight_2667, hPair_1_1, hPair_1_3, hPair_1_7, hPair_1_21, hPair_1_127, hPair_1_381, hPair_1_889, hPair_1_2667, hPair_7_1, hPair_7_3, hPair_7_7, hPair_7_21, hPair_7_127, hPair_7_381, hPair_7_889, hPair_7_2667, hPair_127_1, hPair_127_3, hPair_127_7, hPair_127_21, hPair_127_127, hPair_127_381, hPair_127_889, hPair_127_2667, hPair_889_1, hPair_889_3, hPair_889_7, hPair_889_21, hPair_889_127, hPair_889_381, hPair_889_889, hPair_889_2667]

theorem periodicMainPair_889_2667_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 889 2667) = (0 : ℚ) / 1 := by
  have hneq : 889 ≠ 2667 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 889 = (5 : ℚ) / 571536 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 2667 = (5 : ℚ) / 2286144 := by
    native_decide
  have hvalue : ((5 : ℚ) / 571536) * ((5 : ℚ) / 2286144) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_889_2667_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne018Pairs : Finset (ℕ × ℕ) :=
  [(889, 2667)].toFinset

theorem PeriodicMainRecordsZeroResidualOne018_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne018Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne018Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_889_2667_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
