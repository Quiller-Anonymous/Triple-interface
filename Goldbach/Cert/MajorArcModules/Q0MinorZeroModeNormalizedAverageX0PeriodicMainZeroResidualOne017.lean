import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [17,18). -/

theorem periodicMainPair_887_2661_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 887 2661 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 887 = ([1, 887] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 2661 = ([1, 3, 887, 2661] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 887 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_887 : ramanujanGcdClassCoeffRat 887 887 = (886 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 2661 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 2661 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_887 : ramanujanGcdClassCoeffRat 2661 887 = (-886 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2661 : ramanujanGcdClassCoeffRat 2661 2661 = (1772 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 887 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_887 : ramanujanGcdClassWindowAverageRat X0 887 887 = (2 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 2661 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 2661 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_887 : ramanujanGcdClassWindowAverageRat X0 2661 887 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_2661 : ramanujanGcdClassWindowAverageRat X0 2661 2661 = (2 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 887 2661 887 1 = (2658 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_887 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 887 2661 887 887 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 887 2661 2661 1 = (1772 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 887 2661 2661 3 = (886 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_887 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 887 2661 2661 887 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_2661 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 887 2661 2661 2661 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 887 2661 1 1 = (1772 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 887 2661 1 3 = (886 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_887 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 887 2661 1 887 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2661 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 887 2661 1 2661 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_887_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 887 2661 887 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_887_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 887 2661 887 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_887_887 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 887 2661 887 887 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_887_2661 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 887 2661 887 2661 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_887, hCoeffRight_1, hCoeffRight_3, hCoeffRight_887, hCoeffRight_2661, hAvgLeft_1, hAvgLeft_887, hAvgRight_1, hAvgRight_3, hAvgRight_887, hAvgRight_2661, hBlockLeft_1, hBlockLeft_887, hBlockRight_1, hBlockRight_3, hBlockRight_887, hBlockRight_2661, hPair_1_1, hPair_1_3, hPair_1_887, hPair_1_2661, hPair_887_1, hPair_887_3, hPair_887_887, hPair_887_2661]

theorem periodicMainPair_887_2661_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 887 2661) = (0 : ℚ) / 1 := by
  have hneq : 887 ≠ 2661 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 887 = (5 : ℚ) / 784996 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 2661 = (5 : ℚ) / 3139984 := by
    native_decide
  have hvalue : ((5 : ℚ) / 784996) * ((5 : ℚ) / 3139984) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_887_2661_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne017Pairs : Finset (ℕ × ℕ) :=
  [(887, 2661)].toFinset

theorem PeriodicMainRecordsZeroResidualOne017_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne017Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne017Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_887_2661_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
