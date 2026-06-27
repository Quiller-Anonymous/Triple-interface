import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [11,12). -/

theorem periodicMainPair_211_4431_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 211 4431 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 211 = ([1, 211] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 4431 = ([1, 3, 7, 21, 211, 633, 1477, 4431] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 211 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_211 : ramanujanGcdClassCoeffRat 211 211 = (210 : ℚ) / 1 := by
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
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 211 1 = (1659 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_211 : ramanujanGcdClassWindowAverageRat X0 211 211 = (8 : ℚ) / 1667 := by
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
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 211 1 = (4410 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_211 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 211 211 = (21 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 4431 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 4431 3 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 4431 7 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 4431 21 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_211 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 4431 211 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_633 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 4431 633 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1477 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 4431 1477 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_4431 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 211 4431 4431 4431 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 1 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 1 3 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 1 7 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 1 21 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 1 211 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_633 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 1 633 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_1477 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 1 1477 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_4431 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 1 4431 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 211 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 211 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 211 7 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 211 21 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 211 211 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_633 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 211 633 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_1477 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 211 1477 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_4431 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 211 4431 211 4431 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_211, hCoeffRight_1, hCoeffRight_3, hCoeffRight_7, hCoeffRight_21, hCoeffRight_211, hCoeffRight_633, hCoeffRight_1477, hCoeffRight_4431, hAvgLeft_1, hAvgLeft_211, hAvgRight_1, hAvgRight_3, hAvgRight_7, hAvgRight_21, hAvgRight_211, hAvgRight_633, hAvgRight_1477, hAvgRight_4431, hBlockLeft_1, hBlockLeft_211, hBlockRight_1, hBlockRight_3, hBlockRight_7, hBlockRight_21, hBlockRight_211, hBlockRight_633, hBlockRight_1477, hBlockRight_4431, hPair_1_1, hPair_1_3, hPair_1_7, hPair_1_21, hPair_1_211, hPair_1_633, hPair_1_1477, hPair_1_4431, hPair_211_1, hPair_211_3, hPair_211_7, hPair_211_21, hPair_211_211, hPair_211_633, hPair_211_1477, hPair_211_4431]

theorem periodicMainPair_211_4431_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 211 4431) = (0 : ℚ) / 1 := by
  have hneq : 211 ≠ 4431 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 211 = (1 : ℚ) / 8820 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 4431 = (1 : ℚ) / 1270080 := by
    native_decide
  have hvalue : ((1 : ℚ) / 8820) * ((1 : ℚ) / 1270080) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_211_4431_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne011Pairs : Finset (ℕ × ℕ) :=
  [(211, 4431)].toFinset

theorem PeriodicMainRecordsZeroResidualOne011_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne011Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne011Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_211_4431_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
