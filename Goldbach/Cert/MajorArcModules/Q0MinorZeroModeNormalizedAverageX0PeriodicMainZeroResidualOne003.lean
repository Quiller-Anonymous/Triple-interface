import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [3,4). -/

theorem periodicMainPair_17_4233_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 17 4233 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 17 = ([1, 17] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 4233 = ([1, 3, 17, 51, 83, 249, 1411, 4233] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 17 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_17 : ramanujanGcdClassCoeffRat 17 17 = (16 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 4233 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 4233 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_17 : ramanujanGcdClassCoeffRat 4233 17 = (16 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_51 : ramanujanGcdClassCoeffRat 4233 51 = (-32 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_83 : ramanujanGcdClassCoeffRat 4233 83 = (82 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_249 : ramanujanGcdClassCoeffRat 4233 249 = (-164 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1411 : ramanujanGcdClassCoeffRat 4233 1411 = (-1312 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_4233 : ramanujanGcdClassCoeffRat 4233 4233 = (2624 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 17 1 = (1569 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_17 : ramanujanGcdClassWindowAverageRat X0 17 17 = (98 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 4233 1 = (3100 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 4233 3 = (1550 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_17 : ramanujanGcdClassWindowAverageRat X0 4233 17 = (194 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_51 : ramanujanGcdClassWindowAverageRat X0 4233 51 = (97 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_83 : ramanujanGcdClassWindowAverageRat X0 4233 83 = (38 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_249 : ramanujanGcdClassWindowAverageRat X0 4233 249 = (19 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1411 : ramanujanGcdClassWindowAverageRat X0 4233 1411 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_4233 : ramanujanGcdClassWindowAverageRat X0 4233 4233 = (1 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 17 1 = (3984 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_17 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 17 17 = (249 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 4233 1 = (2624 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 4233 3 = (1312 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_17 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 4233 17 = (164 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_51 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 4233 51 = (82 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_83 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 4233 83 = (32 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_249 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 4233 249 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1411 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 4233 1411 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_4233 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 17 4233 4233 4233 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 1 1 = (2624 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 1 3 = (1312 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 1 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_51 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 1 51 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 1 83 = (32 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_249 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 1 249 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_1411 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 1 1411 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_4233 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 1 4233 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 17 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 17 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 17 17 = (164 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_51 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 17 51 = (82 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 17 83 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_249 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 17 249 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_1411 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 17 1411 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_4233 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 17 4233 17 4233 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_17, hCoeffRight_1, hCoeffRight_3, hCoeffRight_17, hCoeffRight_51, hCoeffRight_83, hCoeffRight_249, hCoeffRight_1411, hCoeffRight_4233, hAvgLeft_1, hAvgLeft_17, hAvgRight_1, hAvgRight_3, hAvgRight_17, hAvgRight_51, hAvgRight_83, hAvgRight_249, hAvgRight_1411, hAvgRight_4233, hBlockLeft_1, hBlockLeft_17, hBlockRight_1, hBlockRight_3, hBlockRight_17, hBlockRight_51, hBlockRight_83, hBlockRight_249, hBlockRight_1411, hBlockRight_4233, hPair_1_1, hPair_1_3, hPair_1_17, hPair_1_51, hPair_1_83, hPair_1_249, hPair_1_1411, hPair_1_4233, hPair_17_1, hPair_17_3, hPair_17_17, hPair_17_51, hPair_17_83, hPair_17_249, hPair_17_1411, hPair_17_4233]

theorem periodicMainPair_17_4233_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 17 4233) = (0 : ℚ) / 1 := by
  have hneq : 17 ≠ 4233 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 17 = (5 : ℚ) / 256 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 4233 = (5 : ℚ) / 6885376 := by
    native_decide
  have hvalue : ((5 : ℚ) / 256) * ((5 : ℚ) / 6885376) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_17_4233_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne003Pairs : Finset (ℕ × ℕ) :=
  [(17, 4233)].toFinset

theorem PeriodicMainRecordsZeroResidualOne003_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne003Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne003Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_17_4233_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
