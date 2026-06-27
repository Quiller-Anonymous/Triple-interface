import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [22,23). -/

theorem periodicMainPair_973_2919_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 973 2919 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 973 = ([1, 7, 139, 973] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 2919 = ([1, 3, 7, 21, 139, 417, 973, 2919] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 973 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 973 7 = (-6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_139 : ramanujanGcdClassCoeffRat 973 139 = (-138 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_973 : ramanujanGcdClassCoeffRat 973 973 = (828 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 2919 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 2919 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 2919 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_21 : ramanujanGcdClassCoeffRat 2919 21 = (-12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_139 : ramanujanGcdClassCoeffRat 2919 139 = (138 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_417 : ramanujanGcdClassCoeffRat 2919 417 = (-276 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_973 : ramanujanGcdClassCoeffRat 2919 973 = (-828 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2919 : ramanujanGcdClassCoeffRat 2919 2919 = (1656 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 973 1 = (1419 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 973 7 = (236 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_139 : ramanujanGcdClassWindowAverageRat X0 973 139 = (10 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_973 : ramanujanGcdClassWindowAverageRat X0 973 973 = (2 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 2919 1 = (946 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 2919 3 = (473 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 2919 7 = (472 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_21 : ramanujanGcdClassWindowAverageRat X0 2919 21 = (236 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_139 : ramanujanGcdClassWindowAverageRat X0 2919 139 = (20 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_417 : ramanujanGcdClassWindowAverageRat X0 2919 417 = (10 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_973 : ramanujanGcdClassWindowAverageRat X0 2919 973 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_2919 : ramanujanGcdClassWindowAverageRat X0 2919 2919 = (2 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 973 1 = (2484 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 973 7 = (414 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_139 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 973 139 = (18 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_973 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 973 973 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 2919 1 = (1656 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 2919 3 = (828 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 2919 7 = (276 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 2919 21 = (138 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_139 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 2919 139 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_417 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 2919 417 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_973 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 2919 973 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_2919 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 973 2919 2919 2919 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 1 1 = (1656 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 1 3 = (828 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 1 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 1 139 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_417 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 1 417 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_973 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 1 973 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2919 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 1 2919 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 7 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 7 7 = (276 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 7 21 = (138 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 7 139 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_417 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 7 417 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_973 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 7 973 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_2919 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 7 2919 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 139 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 139 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 139 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 139 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 139 139 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_417 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 139 417 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_973 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 139 973 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_139_2919 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 139 2919 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 973 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 973 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 973 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 973 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_139 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 973 139 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_417 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 973 417 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_973 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 973 973 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_973_2919 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 973 2919 973 2919 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_7, hCoeffLeft_139, hCoeffLeft_973, hCoeffRight_1, hCoeffRight_3, hCoeffRight_7, hCoeffRight_21, hCoeffRight_139, hCoeffRight_417, hCoeffRight_973, hCoeffRight_2919, hAvgLeft_1, hAvgLeft_7, hAvgLeft_139, hAvgLeft_973, hAvgRight_1, hAvgRight_3, hAvgRight_7, hAvgRight_21, hAvgRight_139, hAvgRight_417, hAvgRight_973, hAvgRight_2919, hBlockLeft_1, hBlockLeft_7, hBlockLeft_139, hBlockLeft_973, hBlockRight_1, hBlockRight_3, hBlockRight_7, hBlockRight_21, hBlockRight_139, hBlockRight_417, hBlockRight_973, hBlockRight_2919, hPair_1_1, hPair_1_3, hPair_1_7, hPair_1_21, hPair_1_139, hPair_1_417, hPair_1_973, hPair_1_2919, hPair_7_1, hPair_7_3, hPair_7_7, hPair_7_21, hPair_7_139, hPair_7_417, hPair_7_973, hPair_7_2919, hPair_139_1, hPair_139_3, hPair_139_7, hPair_139_21, hPair_139_139, hPair_139_417, hPair_139_973, hPair_139_2919, hPair_973_1, hPair_973_3, hPair_973_7, hPair_973_21, hPair_973_139, hPair_973_417, hPair_973_973, hPair_973_2919]

theorem periodicMainPair_973_2919_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 973 2919) = (0 : ℚ) / 1 := by
  have hneq : 973 ≠ 2919 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 973 = (5 : ℚ) / 685584 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 2919 = (5 : ℚ) / 2742336 := by
    native_decide
  have hvalue : ((5 : ℚ) / 685584) * ((5 : ℚ) / 2742336) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_973_2919_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne022Pairs : Finset (ℕ × ℕ) :=
  [(973, 2919)].toFinset

theorem PeriodicMainRecordsZeroResidualOne022_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne022Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne022Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_973_2919_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
