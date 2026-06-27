import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [26,27). -/

theorem periodicMainPair_1591_4773_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 1591 4773 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 1591 = ([1, 37, 43, 1591] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 4773 = ([1, 3, 37, 43, 111, 129, 1591, 4773] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 1591 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_37 : ramanujanGcdClassCoeffRat 1591 37 = (-36 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_43 : ramanujanGcdClassCoeffRat 1591 43 = (-42 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_1591 : ramanujanGcdClassCoeffRat 1591 1591 = (1512 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 4773 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 4773 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_37 : ramanujanGcdClassCoeffRat 4773 37 = (36 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_43 : ramanujanGcdClassCoeffRat 4773 43 = (42 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_111 : ramanujanGcdClassCoeffRat 4773 111 = (-72 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_129 : ramanujanGcdClassCoeffRat 4773 129 = (-84 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1591 : ramanujanGcdClassCoeffRat 4773 1591 = (-1512 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_4773 : ramanujanGcdClassCoeffRat 4773 4773 = (3024 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 1591 1 = (1584 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_37 : ramanujanGcdClassWindowAverageRat X0 1591 37 = (44 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_43 : ramanujanGcdClassWindowAverageRat X0 1591 43 = (38 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_1591 : ramanujanGcdClassWindowAverageRat X0 1591 1591 = (1 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 4773 1 = (1056 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 4773 3 = (528 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_37 : ramanujanGcdClassWindowAverageRat X0 4773 37 = (88 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_43 : ramanujanGcdClassWindowAverageRat X0 4773 43 = (76 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_111 : ramanujanGcdClassWindowAverageRat X0 4773 111 = (44 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_129 : ramanujanGcdClassWindowAverageRat X0 4773 129 = (38 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1591 : ramanujanGcdClassWindowAverageRat X0 4773 1591 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_4773 : ramanujanGcdClassWindowAverageRat X0 4773 4773 = (1 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 1591 1 = (4536 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_37 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 1591 37 = (126 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_43 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 1591 43 = (108 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_1591 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 1591 1591 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 4773 1 = (3024 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 4773 3 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_37 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 4773 37 = (84 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_43 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 4773 43 = (72 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_111 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 4773 111 = (42 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_129 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 4773 129 = (36 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1591 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 4773 1591 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_4773 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 1591 4773 4773 4773 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1 1 = (3024 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1 3 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1 37 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_43 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1 43 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_111 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1 111 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_129 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1 129 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_1591 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1 1591 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_4773 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1 4773 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 37 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 37 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 37 37 = (84 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_43 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 37 43 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_111 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 37 111 = (42 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_129 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 37 129 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_1591 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 37 1591 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_4773 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 37 4773 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 43 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 43 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 43 37 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_43 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 43 43 = (72 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_111 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 43 111 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_129 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 43 129 = (36 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_1591 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 43 1591 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_4773 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 43 4773 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1591 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1591 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1591 37 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_43 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1591 43 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_111 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1591 111 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_129 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1591 129 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_1591 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1591 1591 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_4773 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 1591 4773 1591 4773 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_37, hCoeffLeft_43, hCoeffLeft_1591, hCoeffRight_1, hCoeffRight_3, hCoeffRight_37, hCoeffRight_43, hCoeffRight_111, hCoeffRight_129, hCoeffRight_1591, hCoeffRight_4773, hAvgLeft_1, hAvgLeft_37, hAvgLeft_43, hAvgLeft_1591, hAvgRight_1, hAvgRight_3, hAvgRight_37, hAvgRight_43, hAvgRight_111, hAvgRight_129, hAvgRight_1591, hAvgRight_4773, hBlockLeft_1, hBlockLeft_37, hBlockLeft_43, hBlockLeft_1591, hBlockRight_1, hBlockRight_3, hBlockRight_37, hBlockRight_43, hBlockRight_111, hBlockRight_129, hBlockRight_1591, hBlockRight_4773, hPair_1_1, hPair_1_3, hPair_1_37, hPair_1_43, hPair_1_111, hPair_1_129, hPair_1_1591, hPair_1_4773, hPair_37_1, hPair_37_3, hPair_37_37, hPair_37_43, hPair_37_111, hPair_37_129, hPair_37_1591, hPair_37_4773, hPair_43_1, hPair_43_3, hPair_43_37, hPair_43_43, hPair_43_111, hPair_43_129, hPair_43_1591, hPair_43_4773, hPair_1591_1, hPair_1591_3, hPair_1591_37, hPair_1591_43, hPair_1591_111, hPair_1591_129, hPair_1591_1591, hPair_1591_4773]

theorem periodicMainPair_1591_4773_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 1591 4773) = (0 : ℚ) / 1 := by
  have hneq : 1591 ≠ 4773 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 1591 = (5 : ℚ) / 2286144 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 4773 = (5 : ℚ) / 9144576 := by
    native_decide
  have hvalue : ((5 : ℚ) / 2286144) * ((5 : ℚ) / 9144576) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_1591_4773_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne026Pairs : Finset (ℕ × ℕ) :=
  [(1591, 4773)].toFinset

theorem PeriodicMainRecordsZeroResidualOne026_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne026Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne026Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_1591_4773_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
