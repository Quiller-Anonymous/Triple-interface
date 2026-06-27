import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [2,3). -/

theorem periodicMainPair_7_4431_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 7 4431 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 7 = ([1, 7] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 4431 = ([1, 3, 7, 21, 211, 633, 1477, 4431] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_7 : ramanujanGcdClassCoeffRat 7 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 4431 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 4431 3 = (2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_7 : ramanujanGcdClassCoeffRat 4431 7 = (6 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_21 : ramanujanGcdClassCoeffRat 4431 21 = (-12 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_211 : ramanujanGcdClassCoeffRat 4431 211 = (210 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_633 : ramanujanGcdClassCoeffRat 4431 633 = (-420 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1477 : ramanujanGcdClassCoeffRat 4431 1477 = (-1260 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_4431 : ramanujanGcdClassCoeffRat 4431 4431 = (2520 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_7 : ramanujanGcdClassWindowAverageRat X0 7 7 = (238 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 4431 1 = (948 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 4431 3 = (474 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_7 : ramanujanGcdClassWindowAverageRat X0 4431 7 = (158 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_21 : ramanujanGcdClassWindowAverageRat X0 4431 21 = (79 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_211 : ramanujanGcdClassWindowAverageRat X0 4431 211 = (14 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_633 : ramanujanGcdClassWindowAverageRat X0 4431 633 = (7 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1477 : ramanujanGcdClassWindowAverageRat X0 4431 1477 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_4431 : ramanujanGcdClassWindowAverageRat X0 4431 4431 = (1 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 7 1 = (3798 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 7 7 = (633 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 3 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 7 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 21 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_211 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 211 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_633 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 633 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1477 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 1477 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_4431 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 4431 4431 4431 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 3 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 211 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_633 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 633 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_1477 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 1477 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_4431 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 1 4431 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 7 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 21 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 211 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_633 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 633 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1477 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 1477 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_4431 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 4431 7 4431 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_7, hCoeffRight_1, hCoeffRight_3, hCoeffRight_7, hCoeffRight_21, hCoeffRight_211, hCoeffRight_633, hCoeffRight_1477, hCoeffRight_4431, hAvgLeft_1, hAvgLeft_7, hAvgRight_1, hAvgRight_3, hAvgRight_7, hAvgRight_21, hAvgRight_211, hAvgRight_633, hAvgRight_1477, hAvgRight_4431, hBlockLeft_1, hBlockLeft_7, hBlockRight_1, hBlockRight_3, hBlockRight_7, hBlockRight_21, hBlockRight_211, hBlockRight_633, hBlockRight_1477, hBlockRight_4431, hPair_1_1, hPair_1_3, hPair_1_7, hPair_1_21, hPair_1_211, hPair_1_633, hPair_1_1477, hPair_1_4431, hPair_7_1, hPair_7_3, hPair_7_7, hPair_7_21, hPair_7_211, hPair_7_633, hPair_7_1477, hPair_7_4431]

theorem periodicMainPair_7_4431_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 7 4431) = (0 : ℚ) / 1 := by
  have hneq : 7 ≠ 4431 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 7 = (5 : ℚ) / 36 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 4431 = (1 : ℚ) / 1270080 := by
    native_decide
  have hvalue : ((5 : ℚ) / 36) * ((1 : ℚ) / 1270080) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_7_4431_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne002Pairs : Finset (ℕ × ℕ) :=
  [(7, 4431)].toFinset

theorem PeriodicMainRecordsZeroResidualOne002_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne002Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne002Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_7_4431_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
