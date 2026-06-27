import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [25,26). -/

theorem periodicMainPair_1513_4539_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 1513 4539 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 1513 = ([1, 17, 89, 1513] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 4539 = ([1, 3, 17, 51, 89, 267, 1513, 4539] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 1513 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_17 : ramanujanGcdClassCoeffRat 1513 17 = (-16 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_89 : ramanujanGcdClassCoeffRat 1513 89 = (-88 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_1513 : ramanujanGcdClassCoeffRat 1513 1513 = (1408 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 4539 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 4539 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_17 : ramanujanGcdClassCoeffRat 4539 17 = (16 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_51 : ramanujanGcdClassCoeffRat 4539 51 = (-32 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_89 : ramanujanGcdClassCoeffRat 4539 89 = (88 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_267 : ramanujanGcdClassCoeffRat 4539 267 = (-176 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1513 : ramanujanGcdClassCoeffRat 4539 1513 = (-1408 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_4539 : ramanujanGcdClassCoeffRat 4539 4539 = (2816 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 1513 1 = (1551 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_17 : ramanujanGcdClassWindowAverageRat X0 1513 17 = (97 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_89 : ramanujanGcdClassWindowAverageRat X0 1513 89 = (18 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_1513 : ramanujanGcdClassWindowAverageRat X0 1513 1513 = (1 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 4539 1 = (1034 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 4539 3 = (517 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_17 : ramanujanGcdClassWindowAverageRat X0 4539 17 = (194 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_51 : ramanujanGcdClassWindowAverageRat X0 4539 51 = (97 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_89 : ramanujanGcdClassWindowAverageRat X0 4539 89 = (12 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_267 : ramanujanGcdClassWindowAverageRat X0 4539 267 = (6 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1513 : ramanujanGcdClassWindowAverageRat X0 4539 1513 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_4539 : ramanujanGcdClassWindowAverageRat X0 4539 4539 = (1 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 1513 1 = (4224 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_17 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 1513 17 = (264 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_89 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 1513 89 = (48 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_1513 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 1513 1513 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 4539 1 = (2816 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 4539 3 = (1408 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_17 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 4539 17 = (176 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_51 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 4539 51 = (88 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_89 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 4539 89 = (32 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_267 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 4539 267 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1513 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 4539 1513 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_4539 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1513 4539 4539 4539 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1 1 = (2816 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1 3 = (1408 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_51 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1 51 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1 89 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_267 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1 267 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1 1513 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_4539 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1 4539 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 17 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 17 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 17 17 = (176 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_51 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 17 51 = (88 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 17 89 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_267 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 17 267 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 17 1513 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_4539 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 17 4539 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 89 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 89 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 89 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_51 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 89 51 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 89 89 = (32 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_267 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 89 267 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 89 1513 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_4539 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 89 4539 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1513 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1513 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1513 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_51 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1513 51 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1513 89 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_267 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1513 267 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1513 1513 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_4539 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1513 4539 1513 4539 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_17, hCoeffLeft_89, hCoeffLeft_1513, hCoeffRight_1, hCoeffRight_3, hCoeffRight_17, hCoeffRight_51, hCoeffRight_89, hCoeffRight_267, hCoeffRight_1513, hCoeffRight_4539, hAvgLeft_1, hAvgLeft_17, hAvgLeft_89, hAvgLeft_1513, hAvgRight_1, hAvgRight_3, hAvgRight_17, hAvgRight_51, hAvgRight_89, hAvgRight_267, hAvgRight_1513, hAvgRight_4539, hBlockLeft_1, hBlockLeft_17, hBlockLeft_89, hBlockLeft_1513, hBlockRight_1, hBlockRight_3, hBlockRight_17, hBlockRight_51, hBlockRight_89, hBlockRight_267, hBlockRight_1513, hBlockRight_4539, hPair_1_1, hPair_1_3, hPair_1_17, hPair_1_51, hPair_1_89, hPair_1_267, hPair_1_1513, hPair_1_4539, hPair_17_1, hPair_17_3, hPair_17_17, hPair_17_51, hPair_17_89, hPair_17_267, hPair_17_1513, hPair_17_4539, hPair_89_1, hPair_89_3, hPair_89_17, hPair_89_51, hPair_89_89, hPair_89_267, hPair_89_1513, hPair_89_4539, hPair_1513_1, hPair_1513_3, hPair_1513_17, hPair_1513_51, hPair_1513_89, hPair_1513_267, hPair_1513_1513, hPair_1513_4539]

theorem periodicMainPair_1513_4539_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 1513 4539) = (0 : ℚ) / 1 := by
  have hneq : 1513 ≠ 4539 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 1513 = (5 : ℚ) / 1982464 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 4539 = (5 : ℚ) / 7929856 := by
    native_decide
  have hvalue : ((5 : ℚ) / 1982464) * ((5 : ℚ) / 7929856) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_1513_4539_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne025Pairs : Finset (ℕ × ℕ) :=
  [(1513, 4539)].toFinset

theorem PeriodicMainRecordsZeroResidualOne025_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne025Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne025Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_1513_4539_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
