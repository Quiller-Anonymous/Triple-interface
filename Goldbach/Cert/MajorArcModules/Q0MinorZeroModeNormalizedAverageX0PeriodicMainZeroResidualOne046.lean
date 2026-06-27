import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [46,47). -/

theorem periodicMainPair_4431_211_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 4431 211 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 4431 = ([1, 3, 7, 21, 211, 633, 1477, 4431] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 211 = ([1, 211] : List ℕ).toFinset := by
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
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 211 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_211 : ramanujanGcdClassCoeffRat 211 211 = (210 : ℚ) / 1 := by
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
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 211 1 = (1659 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_211 : ramanujanGcdClassWindowAverageRat X0 211 211 = (8 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 4431 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 4431 3 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 4431 7 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 4431 21 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_211 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 4431 211 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_633 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 4431 633 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_1477 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 4431 1477 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_4431 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 4431 4431 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 211 1 = (4410 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_211 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 4431 211 211 211 = (21 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 1 1 = (2520 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 1 211 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 3 1 = (1260 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 3 211 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 7 1 = (420 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_7_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 7 211 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 21 1 = (210 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_21_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 21 211 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 211 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_211_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 211 211 = (12 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_633_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 633 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_633_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 633 211 = (6 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1477_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 1477 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1477_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 1477 211 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4431_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 4431 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_4431_211 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 4431 211 4431 211 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_7, hCoeffLeft_21, hCoeffLeft_211, hCoeffLeft_633, hCoeffLeft_1477, hCoeffLeft_4431, hCoeffRight_1, hCoeffRight_211, hAvgLeft_1, hAvgLeft_3, hAvgLeft_7, hAvgLeft_21, hAvgLeft_211, hAvgLeft_633, hAvgLeft_1477, hAvgLeft_4431, hAvgRight_1, hAvgRight_211, hBlockLeft_1, hBlockLeft_3, hBlockLeft_7, hBlockLeft_21, hBlockLeft_211, hBlockLeft_633, hBlockLeft_1477, hBlockLeft_4431, hBlockRight_1, hBlockRight_211, hPair_1_1, hPair_1_211, hPair_3_1, hPair_3_211, hPair_7_1, hPair_7_211, hPair_21_1, hPair_21_211, hPair_211_1, hPair_211_211, hPair_633_1, hPair_633_211, hPair_1477_1, hPair_1477_211, hPair_4431_1, hPair_4431_211]

theorem periodicMainPair_4431_211_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 4431 211) = (0 : ℚ) / 1 := by
  have hneq : 4431 ≠ 211 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 4431 = (1 : ℚ) / 1270080 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 211 = (1 : ℚ) / 8820 := by
    native_decide
  have hvalue : ((1 : ℚ) / 1270080) * ((1 : ℚ) / 8820) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_4431_211_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne046Pairs : Finset (ℕ × ℕ) :=
  [(4431, 211)].toFinset

theorem PeriodicMainRecordsZeroResidualOne046_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne046Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne046Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_4431_211_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
