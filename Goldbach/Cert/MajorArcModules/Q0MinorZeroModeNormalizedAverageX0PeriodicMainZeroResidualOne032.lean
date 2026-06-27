import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [32,33). -/

theorem periodicMainPair_2661_887_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2661 887 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2661 = ([1, 3, 887, 2661] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 887 = ([1, 887] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2661 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2661 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_887 : ramanujanGcdClassCoeffRat 2661 887 = (-886 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2661 : ramanujanGcdClassCoeffRat 2661 2661 = (1772 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 887 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_887 : ramanujanGcdClassCoeffRat 887 887 = (886 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2661 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2661 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_887 : ramanujanGcdClassWindowAverageRat X0 2661 887 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2661 : ramanujanGcdClassWindowAverageRat X0 2661 2661 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 887 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_887 : ramanujanGcdClassWindowAverageRat X0 887 887 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2661 887 2661 1 = (1772 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2661 887 2661 3 = (886 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_887 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2661 887 2661 887 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2661 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2661 887 2661 2661 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2661 887 887 1 = (2658 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_887 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2661 887 887 887 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2661 887 1 1 = (1772 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_887 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2661 887 1 887 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2661 887 3 1 = (886 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_887 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2661 887 3 887 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_887_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2661 887 887 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_887_887 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2661 887 887 887 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2661_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2661 887 2661 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2661_887 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2661 887 2661 887 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_887, hCoeffLeft_2661, hCoeffRight_1, hCoeffRight_887, hAvgLeft_1, hAvgLeft_3, hAvgLeft_887, hAvgLeft_2661, hAvgRight_1, hAvgRight_887, hBlockLeft_1, hBlockLeft_3, hBlockLeft_887, hBlockLeft_2661, hBlockRight_1, hBlockRight_887, hPair_1_1, hPair_1_887, hPair_3_1, hPair_3_887, hPair_887_1, hPair_887_887, hPair_2661_1, hPair_2661_887]

theorem periodicMainPair_2661_887_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2661 887) = (0 : ℚ) / 1 := by
  have hneq : 2661 ≠ 887 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2661 = (5 : ℚ) / 3139984 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 887 = (5 : ℚ) / 784996 := by
    native_decide
  have hvalue : ((5 : ℚ) / 3139984) * ((5 : ℚ) / 784996) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2661_887_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne032Pairs : Finset (ℕ × ℕ) :=
  [(2661, 887)].toFinset

theorem PeriodicMainRecordsZeroResidualOne032_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne032Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne032Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2661_887_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
