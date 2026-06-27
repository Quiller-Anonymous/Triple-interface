import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [37,38). -/

theorem periodicMainPair_2841_947_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2841 947 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2841 = ([1, 3, 947, 2841] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 947 = ([1, 947] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2841 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2841 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_947 : ramanujanGcdClassCoeffRat 2841 947 = (-946 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2841 : ramanujanGcdClassCoeffRat 2841 2841 = (1892 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 947 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_947 : ramanujanGcdClassCoeffRat 947 947 = (946 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2841 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2841 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_947 : ramanujanGcdClassWindowAverageRat X0 2841 947 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2841 : ramanujanGcdClassWindowAverageRat X0 2841 2841 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 947 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_947 : ramanujanGcdClassWindowAverageRat X0 947 947 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2841 947 2841 1 = (1892 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2841 947 2841 3 = (946 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_947 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2841 947 2841 947 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2841 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2841 947 2841 2841 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2841 947 947 1 = (2838 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_947 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2841 947 947 947 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2841 947 1 1 = (1892 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_947 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2841 947 1 947 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2841 947 3 1 = (946 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_947 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2841 947 3 947 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_947_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2841 947 947 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_947_947 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2841 947 947 947 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2841_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2841 947 2841 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2841_947 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2841 947 2841 947 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_947, hCoeffLeft_2841, hCoeffRight_1, hCoeffRight_947, hAvgLeft_1, hAvgLeft_3, hAvgLeft_947, hAvgLeft_2841, hAvgRight_1, hAvgRight_947, hBlockLeft_1, hBlockLeft_3, hBlockLeft_947, hBlockLeft_2841, hBlockRight_1, hBlockRight_947, hPair_1_1, hPair_1_947, hPair_3_1, hPair_3_947, hPair_947_1, hPair_947_947, hPair_2841_1, hPair_2841_947]

theorem periodicMainPair_2841_947_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2841 947) = (0 : ℚ) / 1 := by
  have hneq : 2841 ≠ 947 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2841 = (5 : ℚ) / 3579664 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 947 = (5 : ℚ) / 894916 := by
    native_decide
  have hvalue : ((5 : ℚ) / 3579664) * ((5 : ℚ) / 894916) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2841_947_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne037Pairs : Finset (ℕ × ℕ) :=
  [(2841, 947)].toFinset

theorem PeriodicMainRecordsZeroResidualOne037_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne037Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne037Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2841_947_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
