import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [30,31). -/

theorem periodicMainPair_2589_863_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2589 863 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2589 = ([1, 3, 863, 2589] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 863 = ([1, 863] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2589 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2589 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_863 : ramanujanGcdClassCoeffRat 2589 863 = (-862 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2589 : ramanujanGcdClassCoeffRat 2589 2589 = (1724 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 863 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_863 : ramanujanGcdClassCoeffRat 863 863 = (862 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2589 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2589 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_863 : ramanujanGcdClassWindowAverageRat X0 2589 863 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2589 : ramanujanGcdClassWindowAverageRat X0 2589 2589 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 863 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_863 : ramanujanGcdClassWindowAverageRat X0 863 863 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2589 863 2589 1 = (1724 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2589 863 2589 3 = (862 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_863 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2589 863 2589 863 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2589 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2589 863 2589 2589 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2589 863 863 1 = (2586 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_863 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2589 863 863 863 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2589 863 1 1 = (1724 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_863 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2589 863 1 863 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2589 863 3 1 = (862 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_863 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2589 863 3 863 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_863_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2589 863 863 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_863_863 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2589 863 863 863 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2589_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2589 863 2589 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2589_863 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2589 863 2589 863 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_863, hCoeffLeft_2589, hCoeffRight_1, hCoeffRight_863, hAvgLeft_1, hAvgLeft_3, hAvgLeft_863, hAvgLeft_2589, hAvgRight_1, hAvgRight_863, hBlockLeft_1, hBlockLeft_3, hBlockLeft_863, hBlockLeft_2589, hBlockRight_1, hBlockRight_863, hPair_1_1, hPair_1_863, hPair_3_1, hPair_3_863, hPair_863_1, hPair_863_863, hPair_2589_1, hPair_2589_863]

theorem periodicMainPair_2589_863_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2589 863) = (0 : ℚ) / 1 := by
  have hneq : 2589 ≠ 863 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2589 = (5 : ℚ) / 2972176 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 863 = (5 : ℚ) / 743044 := by
    native_decide
  have hvalue : ((5 : ℚ) / 2972176) * ((5 : ℚ) / 743044) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2589_863_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne030Pairs : Finset (ℕ × ℕ) :=
  [(2589, 863)].toFinset

theorem PeriodicMainRecordsZeroResidualOne030_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne030Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne030Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2589_863_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
