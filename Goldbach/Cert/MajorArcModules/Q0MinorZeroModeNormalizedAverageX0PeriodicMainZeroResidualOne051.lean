import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [51,52). -/

theorem periodicMainPair_4773_37_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 4773 37 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 4773 = ([1, 3, 37, 43, 111, 129, 1591, 4773] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 37 = ([1, 37] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 4773 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 4773 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_37 : ramanujanGcdClassCoeffRat 4773 37 = (36 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_43 : ramanujanGcdClassCoeffRat 4773 43 = (42 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_111 : ramanujanGcdClassCoeffRat 4773 111 = (-72 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_129 : ramanujanGcdClassCoeffRat 4773 129 = (-84 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_1591 : ramanujanGcdClassCoeffRat 4773 1591 = (-1512 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_4773 : ramanujanGcdClassCoeffRat 4773 4773 = (3024 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 37 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_37 : ramanujanGcdClassCoeffRat 37 37 = (36 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 4773 1 = (1056 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 4773 3 = (528 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_37 : ramanujanGcdClassWindowAverageRat X0 4773 37 = (88 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_43 : ramanujanGcdClassWindowAverageRat X0 4773 43 = (76 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_111 : ramanujanGcdClassWindowAverageRat X0 4773 111 = (44 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_129 : ramanujanGcdClassWindowAverageRat X0 4773 129 = (38 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_1591 : ramanujanGcdClassWindowAverageRat X0 4773 1591 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_4773 : ramanujanGcdClassWindowAverageRat X0 4773 4773 = (1 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 37 1 = (1622 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_37 : ramanujanGcdClassWindowAverageRat X0 37 37 = (45 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 4773 1 = (3024 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 4773 3 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_37 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 4773 37 = (84 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_43 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 4773 43 = (72 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_111 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 4773 111 = (42 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_129 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 4773 129 = (36 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_1591 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 4773 1591 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_4773 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 4773 4773 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 37 1 = (4644 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_37 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4773 37 37 37 = (129 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 1 1 = (3024 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 1 37 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 3 1 = (1512 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 3 37 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 37 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_37_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 37 37 = (84 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 43 1 = (72 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_43_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 43 37 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_111_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 111 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_111_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 111 37 = (42 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_129_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 129 1 = (36 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_129_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 129 37 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 1591 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1591_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 1591 37 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4773_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 4773 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4773_37 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4773 37 4773 37 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_37, hCoeffLeft_43, hCoeffLeft_111, hCoeffLeft_129, hCoeffLeft_1591, hCoeffLeft_4773, hCoeffRight_1, hCoeffRight_37, hAvgLeft_1, hAvgLeft_3, hAvgLeft_37, hAvgLeft_43, hAvgLeft_111, hAvgLeft_129, hAvgLeft_1591, hAvgLeft_4773, hAvgRight_1, hAvgRight_37, hBlockLeft_1, hBlockLeft_3, hBlockLeft_37, hBlockLeft_43, hBlockLeft_111, hBlockLeft_129, hBlockLeft_1591, hBlockLeft_4773, hBlockRight_1, hBlockRight_37, hPair_1_1, hPair_1_37, hPair_3_1, hPair_3_37, hPair_37_1, hPair_37_37, hPair_43_1, hPair_43_37, hPair_111_1, hPair_111_37, hPair_129_1, hPair_129_37, hPair_1591_1, hPair_1591_37, hPair_4773_1, hPair_4773_37]

theorem periodicMainPair_4773_37_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 4773 37) = (0 : ℚ) / 1 := by
  have hneq : 4773 ≠ 37 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 4773 = (5 : ℚ) / 9144576 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 37 = (5 : ℚ) / 1296 := by
    native_decide
  have hvalue : ((5 : ℚ) / 9144576) * ((5 : ℚ) / 1296) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_4773_37_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne051Pairs : Finset (ℕ × ℕ) :=
  [(4773, 37)].toFinset

theorem PeriodicMainRecordsZeroResidualOne051_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne051Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne051Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_4773_37_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
