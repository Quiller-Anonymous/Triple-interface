import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [45,46). -/

theorem periodicMainPair_4431_7_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 4431 7 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 4431 = ([1, 3, 7, 21, 211, 633, 1477, 4431] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 7 = ([1, 7] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 4431 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 4431 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 4431 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_21 : ramanujanGcdClassCoeffRat 4431 21 = (-12 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_211 : ramanujanGcdClassCoeffRat 4431 211 = (210 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_633 : ramanujanGcdClassCoeffRat 4431 633 = (-420 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_1477 : ramanujanGcdClassCoeffRat 4431 1477 = (-1260 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_4431 : ramanujanGcdClassCoeffRat 4431 4431 = (2520 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 7 7 = (6 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 4431 1 = (948 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 4431 3 = (474 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 4431 7 = (158 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_21 : ramanujanGcdClassWindowAverageRat X0 4431 21 = (79 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_211 : ramanujanGcdClassWindowAverageRat X0 4431 211 = (14 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_633 : ramanujanGcdClassWindowAverageRat X0 4431 633 = (7 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_1477 : ramanujanGcdClassWindowAverageRat X0 4431 1477 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_4431 : ramanujanGcdClassWindowAverageRat X0 4431 4431 = (1 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 7 7 = (238 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 4431 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 4431 3 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 4431 7 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 4431 21 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_211 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 4431 211 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_633 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 4431 633 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_1477 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 4431 1477 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_4431 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 4431 4431 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 7 1 = (3798 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 7 7 7 = (633 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 1 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 3 1 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 3 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 7 7 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 21 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 21 7 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 211 1 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 211 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_633_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 633 1 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_633_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 633 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1477_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 1477 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1477_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 1477 7 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4431_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 4431 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4431_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 7 4431 7 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_7, hCoeffLeft_21, hCoeffLeft_211, hCoeffLeft_633, hCoeffLeft_1477, hCoeffLeft_4431, hCoeffRight_1, hCoeffRight_7, hAvgLeft_1, hAvgLeft_3, hAvgLeft_7, hAvgLeft_21, hAvgLeft_211, hAvgLeft_633, hAvgLeft_1477, hAvgLeft_4431, hAvgRight_1, hAvgRight_7, hBlockLeft_1, hBlockLeft_3, hBlockLeft_7, hBlockLeft_21, hBlockLeft_211, hBlockLeft_633, hBlockLeft_1477, hBlockLeft_4431, hBlockRight_1, hBlockRight_7, hPair_1_1, hPair_1_7, hPair_3_1, hPair_3_7, hPair_7_1, hPair_7_7, hPair_21_1, hPair_21_7, hPair_211_1, hPair_211_7, hPair_633_1, hPair_633_7, hPair_1477_1, hPair_1477_7, hPair_4431_1, hPair_4431_7]

theorem periodicMainPair_4431_7_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 4431 7) = (0 : ℚ) / 1 := by
  have hneq : 4431 ≠ 7 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 4431 = (1 : ℚ) / 1270080 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 7 = (5 : ℚ) / 36 := by
    native_decide
  have hvalue : ((1 : ℚ) / 1270080) * ((5 : ℚ) / 36) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_4431_7_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne045Pairs : Finset (ℕ × ℕ) :=
  [(4431, 7)].toFinset

theorem PeriodicMainRecordsZeroResidualOne045_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne045Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne045Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_4431_7_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
