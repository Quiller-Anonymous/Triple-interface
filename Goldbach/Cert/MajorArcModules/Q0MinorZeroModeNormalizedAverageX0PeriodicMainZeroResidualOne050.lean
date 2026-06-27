import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [50,51). -/

theorem periodicMainPair_4539_1513_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 4539 1513 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 4539 = ([1, 3, 17, 51, 89, 267, 1513, 4539] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 1513 = ([1, 17, 89, 1513] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 4539 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 4539 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_17 : ramanujanGcdClassCoeffRat 4539 17 = (16 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_51 : ramanujanGcdClassCoeffRat 4539 51 = (-32 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_89 : ramanujanGcdClassCoeffRat 4539 89 = (88 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_267 : ramanujanGcdClassCoeffRat 4539 267 = (-176 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_1513 : ramanujanGcdClassCoeffRat 4539 1513 = (-1408 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_4539 : ramanujanGcdClassCoeffRat 4539 4539 = (2816 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 1513 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_17 : ramanujanGcdClassCoeffRat 1513 17 = (-16 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_89 : ramanujanGcdClassCoeffRat 1513 89 = (-88 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1513 : ramanujanGcdClassCoeffRat 1513 1513 = (1408 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 4539 1 = (1034 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 4539 3 = (517 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_17 : ramanujanGcdClassWindowAverageRat X0 4539 17 = (194 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_51 : ramanujanGcdClassWindowAverageRat X0 4539 51 = (97 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_89 : ramanujanGcdClassWindowAverageRat X0 4539 89 = (12 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_267 : ramanujanGcdClassWindowAverageRat X0 4539 267 = (6 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_1513 : ramanujanGcdClassWindowAverageRat X0 4539 1513 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_4539 : ramanujanGcdClassWindowAverageRat X0 4539 4539 = (1 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 1513 1 = (1551 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_17 : ramanujanGcdClassWindowAverageRat X0 1513 17 = (97 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_89 : ramanujanGcdClassWindowAverageRat X0 1513 89 = (18 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1513 : ramanujanGcdClassWindowAverageRat X0 1513 1513 = (1 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 4539 1 = (2816 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 4539 3 = (1408 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_17 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 4539 17 = (176 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_51 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 4539 51 = (88 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_89 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 4539 89 = (32 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_267 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 4539 267 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_1513 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 4539 1513 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_4539 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 4539 4539 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 1513 1 = (4224 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_17 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 1513 17 = (264 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_89 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 1513 89 = (48 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1513 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4539 1513 1513 1513 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 1 1 = (2816 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 1 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 1 89 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 1 1513 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 3 1 = (1408 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 3 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 3 89 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 3 1513 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 17 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 17 17 = (176 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 17 89 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_17_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 17 1513 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_51_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 51 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_51_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 51 17 = (88 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_51_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 51 89 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_51_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 51 1513 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 89 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 89 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 89 89 = (32 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_89_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 89 1513 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_267_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 267 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_267_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 267 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_267_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 267 89 = (16 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_267_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 267 1513 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 1513 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 1513 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 1513 89 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1513_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 1513 1513 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4539_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 4539 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4539_17 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 4539 17 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4539_89 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 4539 89 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4539_1513 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4539 1513 4539 1513 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_17, hCoeffLeft_51, hCoeffLeft_89, hCoeffLeft_267, hCoeffLeft_1513, hCoeffLeft_4539, hCoeffRight_1, hCoeffRight_17, hCoeffRight_89, hCoeffRight_1513, hAvgLeft_1, hAvgLeft_3, hAvgLeft_17, hAvgLeft_51, hAvgLeft_89, hAvgLeft_267, hAvgLeft_1513, hAvgLeft_4539, hAvgRight_1, hAvgRight_17, hAvgRight_89, hAvgRight_1513, hBlockLeft_1, hBlockLeft_3, hBlockLeft_17, hBlockLeft_51, hBlockLeft_89, hBlockLeft_267, hBlockLeft_1513, hBlockLeft_4539, hBlockRight_1, hBlockRight_17, hBlockRight_89, hBlockRight_1513, hPair_1_1, hPair_1_17, hPair_1_89, hPair_1_1513, hPair_3_1, hPair_3_17, hPair_3_89, hPair_3_1513, hPair_17_1, hPair_17_17, hPair_17_89, hPair_17_1513, hPair_51_1, hPair_51_17, hPair_51_89, hPair_51_1513, hPair_89_1, hPair_89_17, hPair_89_89, hPair_89_1513, hPair_267_1, hPair_267_17, hPair_267_89, hPair_267_1513, hPair_1513_1, hPair_1513_17, hPair_1513_89, hPair_1513_1513, hPair_4539_1, hPair_4539_17, hPair_4539_89, hPair_4539_1513]

theorem periodicMainPair_4539_1513_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 4539 1513) = (0 : ℚ) / 1 := by
  have hneq : 4539 ≠ 1513 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 4539 = (5 : ℚ) / 7929856 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 1513 = (5 : ℚ) / 1982464 := by
    native_decide
  have hvalue : ((5 : ℚ) / 7929856) * ((5 : ℚ) / 1982464) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_4539_1513_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne050Pairs : Finset (ℕ × ℕ) :=
  [(4539, 1513)].toFinset

theorem PeriodicMainRecordsZeroResidualOne050_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne050Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne050Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_4539_1513_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
