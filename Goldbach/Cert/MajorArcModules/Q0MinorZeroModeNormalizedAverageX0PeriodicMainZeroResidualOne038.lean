import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [38,39). -/

theorem periodicMainPair_2913_971_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2913 971 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2913 = ([1, 3, 971, 2913] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 971 = ([1, 971] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2913 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2913 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_971 : ramanujanGcdClassCoeffRat 2913 971 = (-970 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2913 : ramanujanGcdClassCoeffRat 2913 2913 = (1940 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 971 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_971 : ramanujanGcdClassCoeffRat 971 971 = (970 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2913 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2913 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_971 : ramanujanGcdClassWindowAverageRat X0 2913 971 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2913 : ramanujanGcdClassWindowAverageRat X0 2913 2913 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 971 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_971 : ramanujanGcdClassWindowAverageRat X0 971 971 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2913 971 2913 1 = (1940 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2913 971 2913 3 = (970 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_971 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2913 971 2913 971 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2913 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2913 971 2913 2913 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2913 971 971 1 = (2910 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_971 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2913 971 971 971 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2913 971 1 1 = (1940 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_971 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2913 971 1 971 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2913 971 3 1 = (970 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_971 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2913 971 3 971 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_971_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2913 971 971 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_971_971 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2913 971 971 971 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2913_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2913 971 2913 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2913_971 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2913 971 2913 971 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_971, hCoeffLeft_2913, hCoeffRight_1, hCoeffRight_971, hAvgLeft_1, hAvgLeft_3, hAvgLeft_971, hAvgLeft_2913, hAvgRight_1, hAvgRight_971, hBlockLeft_1, hBlockLeft_3, hBlockLeft_971, hBlockLeft_2913, hBlockRight_1, hBlockRight_971, hPair_1_1, hPair_1_971, hPair_3_1, hPair_3_971, hPair_971_1, hPair_971_971, hPair_2913_1, hPair_2913_971]

theorem periodicMainPair_2913_971_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2913 971) = (0 : ℚ) / 1 := by
  have hneq : 2913 ≠ 971 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2913 = (1 : ℚ) / 752720 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 971 = (1 : ℚ) / 188180 := by
    native_decide
  have hvalue : ((1 : ℚ) / 752720) * ((1 : ℚ) / 188180) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2913_971_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne038Pairs : Finset (ℕ × ℕ) :=
  [(2913, 971)].toFinset

theorem PeriodicMainRecordsZeroResidualOne038_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne038Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne038Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2913_971_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
