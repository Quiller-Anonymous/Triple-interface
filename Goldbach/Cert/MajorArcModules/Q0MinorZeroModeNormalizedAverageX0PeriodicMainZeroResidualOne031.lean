import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [31,32). -/

theorem periodicMainPair_2643_881_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2643 881 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2643 = ([1, 3, 881, 2643] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 881 = ([1, 881] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2643 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2643 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_881 : ramanujanGcdClassCoeffRat 2643 881 = (-880 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2643 : ramanujanGcdClassCoeffRat 2643 2643 = (1760 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 881 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_881 : ramanujanGcdClassCoeffRat 881 881 = (880 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2643 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2643 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_881 : ramanujanGcdClassWindowAverageRat X0 2643 881 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2643 : ramanujanGcdClassWindowAverageRat X0 2643 2643 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 881 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_881 : ramanujanGcdClassWindowAverageRat X0 881 881 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2643 881 2643 1 = (1760 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2643 881 2643 3 = (880 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_881 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2643 881 2643 881 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2643 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2643 881 2643 2643 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2643 881 881 1 = (2640 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_881 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2643 881 881 881 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2643 881 1 1 = (1760 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_881 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2643 881 1 881 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2643 881 3 1 = (880 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_881 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2643 881 3 881 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_881_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2643 881 881 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_881_881 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2643 881 881 881 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2643_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2643 881 2643 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2643_881 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2643 881 2643 881 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_881, hCoeffLeft_2643, hCoeffRight_1, hCoeffRight_881, hAvgLeft_1, hAvgLeft_3, hAvgLeft_881, hAvgLeft_2643, hAvgRight_1, hAvgRight_881, hBlockLeft_1, hBlockLeft_3, hBlockLeft_881, hBlockLeft_2643, hBlockRight_1, hBlockRight_881, hPair_1_1, hPair_1_881, hPair_3_1, hPair_3_881, hPair_881_1, hPair_881_881, hPair_2643_1, hPair_2643_881]

theorem periodicMainPair_2643_881_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2643 881) = (0 : ℚ) / 1 := by
  have hneq : 2643 ≠ 881 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2643 = (1 : ℚ) / 619520 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 881 = (1 : ℚ) / 154880 := by
    native_decide
  have hvalue : ((1 : ℚ) / 619520) * ((1 : ℚ) / 154880) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2643_881_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne031Pairs : Finset (ℕ × ℕ) :=
  [(2643, 881)].toFinset

theorem PeriodicMainRecordsZeroResidualOne031_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne031Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne031Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2643_881_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
