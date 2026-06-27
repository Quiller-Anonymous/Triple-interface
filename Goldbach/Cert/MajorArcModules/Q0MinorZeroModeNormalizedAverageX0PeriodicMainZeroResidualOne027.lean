import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [27,28). -/

theorem periodicMainPair_2517_839_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 2517 839 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 2517 = ([1, 3, 839, 2517] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 839 = ([1, 839] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 2517 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_3 : ramanujanGcdClassCoeffRat 2517 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_839 : ramanujanGcdClassCoeffRat 2517 839 = (-838 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_2517 : ramanujanGcdClassCoeffRat 2517 2517 = (1676 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 839 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_839 : ramanujanGcdClassCoeffRat 839 839 = (838 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 2517 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_3 : ramanujanGcdClassWindowAverageRat X0 2517 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_839 : ramanujanGcdClassWindowAverageRat X0 2517 839 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgLeft_2517 : ramanujanGcdClassWindowAverageRat X0 2517 2517 = (2 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 839 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_839 : ramanujanGcdClassWindowAverageRat X0 839 839 = (2 : ℚ) / 1667 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2517 839 2517 1 = (1676 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2517 839 2517 3 = (838 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_839 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2517 839 2517 839 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_2517 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2517 839 2517 2517 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2517 839 839 1 = (2514 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_839 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 2517 839 839 839 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2517 839 1 1 = (1676 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_839 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2517 839 1 839 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2517 839 3 1 = (838 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_3_839 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2517 839 3 839 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_839_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2517 839 839 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_839_839 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2517 839 839 839 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2517_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2517 839 2517 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_2517_839 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 2517 839 2517 839 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_3, hCoeffLeft_839, hCoeffLeft_2517, hCoeffRight_1, hCoeffRight_839, hAvgLeft_1, hAvgLeft_3, hAvgLeft_839, hAvgLeft_2517, hAvgRight_1, hAvgRight_839, hBlockLeft_1, hBlockLeft_3, hBlockLeft_839, hBlockLeft_2517, hBlockRight_1, hBlockRight_839, hPair_1_1, hPair_1_839, hPair_3_1, hPair_3_839, hPair_839_1, hPair_839_839, hPair_2517_1, hPair_2517_839]

theorem periodicMainPair_2517_839_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 2517 839) = (0 : ℚ) / 1 := by
  have hneq : 2517 ≠ 839 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 2517 = (5 : ℚ) / 2808976 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 839 = (5 : ℚ) / 702244 := by
    native_decide
  have hvalue : ((5 : ℚ) / 2808976) * ((5 : ℚ) / 702244) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_2517_839_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne027Pairs : Finset (ℕ × ℕ) :=
  [(2517, 839)].toFinset

theorem PeriodicMainRecordsZeroResidualOne027_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne027Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne027Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_2517_839_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
