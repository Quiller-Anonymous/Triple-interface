import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [14,15). -/

theorem periodicMainPair_857_2571_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 857 2571 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 857 = ([1, 857] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 2571 = ([1, 3, 857, 2571] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 857 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_857 : ramanujanGcdClassCoeffRat 857 857 = (856 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 2571 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 2571 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_857 : ramanujanGcdClassCoeffRat 2571 857 = (-856 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2571 : ramanujanGcdClassCoeffRat 2571 2571 = (1712 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 857 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_857 : ramanujanGcdClassWindowAverageRat X0 857 857 = (2 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 2571 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 2571 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_857 : ramanujanGcdClassWindowAverageRat X0 2571 857 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_2571 : ramanujanGcdClassWindowAverageRat X0 2571 2571 = (2 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 857 2571 857 1 = (2568 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_857 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 857 2571 857 857 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 857 2571 2571 1 = (1712 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 857 2571 2571 3 = (856 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_857 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 857 2571 2571 857 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_2571 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 857 2571 2571 2571 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 857 2571 1 1 = (1712 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 857 2571 1 3 = (856 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_857 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 857 2571 1 857 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2571 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 857 2571 1 2571 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_857_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 857 2571 857 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_857_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 857 2571 857 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_857_857 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 857 2571 857 857 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_857_2571 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 857 2571 857 2571 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_857, hCoeffRight_1, hCoeffRight_3, hCoeffRight_857, hCoeffRight_2571, hAvgLeft_1, hAvgLeft_857, hAvgRight_1, hAvgRight_3, hAvgRight_857, hAvgRight_2571, hBlockLeft_1, hBlockLeft_857, hBlockRight_1, hBlockRight_3, hBlockRight_857, hBlockRight_2571, hPair_1_1, hPair_1_3, hPair_1_857, hPair_1_2571, hPair_857_1, hPair_857_3, hPair_857_857, hPair_857_2571]

theorem periodicMainPair_857_2571_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 857 2571) = (0 : ℚ) / 1 := by
  have hneq : 857 ≠ 2571 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 857 = (5 : ℚ) / 732736 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 2571 = (5 : ℚ) / 2930944 := by
    native_decide
  have hvalue : ((5 : ℚ) / 732736) * ((5 : ℚ) / 2930944) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_857_2571_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne014Pairs : Finset (ℕ × ℕ) :=
  [(857, 2571)].toFinset

theorem PeriodicMainRecordsZeroResidualOne014_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne014Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne014Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_857_2571_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
