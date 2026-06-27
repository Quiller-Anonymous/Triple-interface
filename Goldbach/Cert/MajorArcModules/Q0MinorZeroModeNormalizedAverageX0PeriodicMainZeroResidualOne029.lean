import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [29,30). -/

theorem periodicMainPair_2571_857_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2571 857 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2571 = ([1, 3, 857, 2571] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 857 = ([1, 857] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2571 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2571 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_857 : ramanujanGcdClassCoeffRat 2571 857 = (-856 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2571 : ramanujanGcdClassCoeffRat 2571 2571 = (1712 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 857 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_857 : ramanujanGcdClassCoeffRat 857 857 = (856 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2571 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2571 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_857 : ramanujanGcdClassWindowAverageRat X0 2571 857 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2571 : ramanujanGcdClassWindowAverageRat X0 2571 2571 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 857 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_857 : ramanujanGcdClassWindowAverageRat X0 857 857 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2571 857 2571 1 = (1712 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2571 857 2571 3 = (856 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_857 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2571 857 2571 857 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2571 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2571 857 2571 2571 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2571 857 857 1 = (2568 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_857 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2571 857 857 857 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2571 857 1 1 = (1712 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_857 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2571 857 1 857 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2571 857 3 1 = (856 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_857 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2571 857 3 857 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_857_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2571 857 857 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_857_857 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2571 857 857 857 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2571_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2571 857 2571 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2571_857 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2571 857 2571 857 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_857, hCoeffLeft_2571, hCoeffRight_1, hCoeffRight_857, hAvgLeft_1, hAvgLeft_3, hAvgLeft_857, hAvgLeft_2571, hAvgRight_1, hAvgRight_857, hBlockLeft_1, hBlockLeft_3, hBlockLeft_857, hBlockLeft_2571, hBlockRight_1, hBlockRight_857, hPair_1_1, hPair_1_857, hPair_3_1, hPair_3_857, hPair_857_1, hPair_857_857, hPair_2571_1, hPair_2571_857]

theorem periodicMainPair_2571_857_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2571 857) = (0 : ℚ) / 1 := by
  have hneq : 2571 ≠ 857 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2571 = (5 : ℚ) / 2930944 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 857 = (5 : ℚ) / 732736 := by
    native_decide
  have hvalue : ((5 : ℚ) / 2930944) * ((5 : ℚ) / 732736) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2571_857_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne029Pairs : Finset (ℕ × ℕ) :=
  [(2571, 857)].toFinset

theorem PeriodicMainRecordsZeroResidualOne029_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne029Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne029Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2571_857_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
