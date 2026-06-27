import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [43,44). -/

theorem periodicMainPair_4233_83_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 4233 83 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 4233 = ([1, 3, 17, 51, 83, 249, 1411, 4233] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 83 = ([1, 83] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 4233 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 4233 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_17 : ramanujanGcdClassCoeffRat 4233 17 = (16 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_51 : ramanujanGcdClassCoeffRat 4233 51 = (-32 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_83 : ramanujanGcdClassCoeffRat 4233 83 = (82 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_249 : ramanujanGcdClassCoeffRat 4233 249 = (-164 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_1411 : ramanujanGcdClassCoeffRat 4233 1411 = (-1312 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_4233 : ramanujanGcdClassCoeffRat 4233 4233 = (2624 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 83 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_83 : ramanujanGcdClassCoeffRat 83 83 = (82 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 4233 1 = (3100 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 4233 3 = (1550 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_17 : ramanujanGcdClassWindowAverageRat X0 4233 17 = (194 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_51 : ramanujanGcdClassWindowAverageRat X0 4233 51 = (97 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_83 : ramanujanGcdClassWindowAverageRat X0 4233 83 = (38 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_249 : ramanujanGcdClassWindowAverageRat X0 4233 249 = (19 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_1411 : ramanujanGcdClassWindowAverageRat X0 4233 1411 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_4233 : ramanujanGcdClassWindowAverageRat X0 4233 4233 = (1 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 83 1 = (1647 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_83 : ramanujanGcdClassWindowAverageRat X0 83 83 = (20 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 4233 1 = (2624 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 4233 3 = (1312 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_17 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 4233 17 = (164 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_51 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 4233 51 = (82 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_83 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 4233 83 = (32 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_249 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 4233 249 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_1411 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 4233 1411 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_4233 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 4233 4233 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 83 1 = (4182 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_83 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4233 83 83 83 = (51 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 1 1 = (2624 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 1 83 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 3 1 = (1312 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 3 83 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 17 1 = (164 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 17 83 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_51_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 51 1 = (82 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_51_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 51 83 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_83_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 83 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_83_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 83 83 = (32 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_249_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 249 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_249_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 249 83 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1411_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 1411 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1411_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 1411 83 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4233_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 4233 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4233_83 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4233 83 4233 83 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_17, hCoeffLeft_51, hCoeffLeft_83, hCoeffLeft_249, hCoeffLeft_1411, hCoeffLeft_4233, hCoeffRight_1, hCoeffRight_83, hAvgLeft_1, hAvgLeft_3, hAvgLeft_17, hAvgLeft_51, hAvgLeft_83, hAvgLeft_249, hAvgLeft_1411, hAvgLeft_4233, hAvgRight_1, hAvgRight_83, hBlockLeft_1, hBlockLeft_3, hBlockLeft_17, hBlockLeft_51, hBlockLeft_83, hBlockLeft_249, hBlockLeft_1411, hBlockLeft_4233, hBlockRight_1, hBlockRight_83, hPair_1_1, hPair_1_83, hPair_3_1, hPair_3_83, hPair_17_1, hPair_17_83, hPair_51_1, hPair_51_83, hPair_83_1, hPair_83_83, hPair_249_1, hPair_249_83, hPair_1411_1, hPair_1411_83, hPair_4233_1, hPair_4233_83]

theorem periodicMainPair_4233_83_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 4233 83) = (0 : ℚ) / 1 := by
  have hneq : 4233 ≠ 83 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 4233 = (5 : ℚ) / 6885376 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 83 = (5 : ℚ) / 6724 := by
    native_decide
  have hvalue : ((5 : ℚ) / 6885376) * ((5 : ℚ) / 6724) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_4233_83_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne043Pairs : Finset (ℕ × ℕ) :=
  [(4233, 83)].toFinset

theorem PeriodicMainRecordsZeroResidualOne043_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne043Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne043Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_4233_83_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
