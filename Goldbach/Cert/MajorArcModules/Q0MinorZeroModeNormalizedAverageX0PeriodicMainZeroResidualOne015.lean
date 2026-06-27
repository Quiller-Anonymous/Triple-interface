import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record proofs for JSON indices [15,16). -/

theorem periodicMainPair_863_2589_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 863 2589 = (0 : ℚ) / 1 := by
  have hDivLeft : Nat.divisors 863 = ([1, 863] : List ℕ).toFinset := by
    native_decide
  have hDivRight : Nat.divisors 2589 = ([1, 3, 863, 2589] : List ℕ).toFinset := by
    native_decide
  have hCoeffLeft_1 : ramanujanGcdClassCoeffRat 863 1 = (-1 : ℚ) / 1 := by
    native_decide
  have hCoeffLeft_863 : ramanujanGcdClassCoeffRat 863 863 = (862 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_1 : ramanujanGcdClassCoeffRat 2589 1 = (1 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_3 : ramanujanGcdClassCoeffRat 2589 3 = (-2 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_863 : ramanujanGcdClassCoeffRat 2589 863 = (-862 : ℚ) / 1 := by
    native_decide
  have hCoeffRight_2589 : ramanujanGcdClassCoeffRat 2589 2589 = (1724 : ℚ) / 1 := by
    native_decide
  have hAvgLeft_1 : ramanujanGcdClassWindowAverageRat X0 863 1 = (1665 : ℚ) / 1667 := by
    native_decide
  have hAvgLeft_863 : ramanujanGcdClassWindowAverageRat X0 863 863 = (2 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_1 : ramanujanGcdClassWindowAverageRat X0 2589 1 = (1110 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_3 : ramanujanGcdClassWindowAverageRat X0 2589 3 = (555 : ℚ) / 1667 := by
    native_decide
  have hAvgRight_863 : ramanujanGcdClassWindowAverageRat X0 2589 863 = (4 : ℚ) / 5001 := by
    native_decide
  have hAvgRight_2589 : ramanujanGcdClassWindowAverageRat X0 2589 2589 = (2 : ℚ) / 5001 := by
    native_decide
  have hBlockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 863 2589 863 1 = (2586 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockLeft_863 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 863 2589 863 863 = (3 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 863 2589 2589 1 = (1724 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 863 2589 2589 3 = (862 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_863 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 863 2589 2589 863 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hBlockRight_2589 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 863 2589 2589 2589 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  have hPair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 863 2589 1 1 = (1724 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 863 2589 1 3 = (862 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_863 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 863 2589 1 863 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_1_2589 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 863 2589 1 2589 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_863_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 863 2589 863 1 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_863_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 863 2589 863 3 = (0 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
    norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_863_863 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 863 2589 863 863 = (2 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  have hPair_863_2589 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 863 2589 863 2589 = (1 : ℚ) := by
    rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
    · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
      all_goals native_decide
    · norm_num [ramanujanGcdClassJointCompatibility]
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat, H, hDivLeft, hDivRight, hCoeffLeft_1, hCoeffLeft_863, hCoeffRight_1, hCoeffRight_3, hCoeffRight_863, hCoeffRight_2589, hAvgLeft_1, hAvgLeft_863, hAvgRight_1, hAvgRight_3, hAvgRight_863, hAvgRight_2589, hBlockLeft_1, hBlockLeft_863, hBlockRight_1, hBlockRight_3, hBlockRight_863, hBlockRight_2589, hPair_1_1, hPair_1_3, hPair_1_863, hPair_1_2589, hPair_863_1, hPair_863_3, hPair_863_863, hPair_863_2589]

theorem periodicMainPair_863_2589_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 863 2589) = (0 : ℚ) / 1 := by
  have hneq : 863 ≠ 2589 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 863 = (5 : ℚ) / 743044 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 2589 = (5 : ℚ) / 2972176 := by
    native_decide
  have hvalue : ((5 : ℚ) / 743044) * ((5 : ℚ) / 2972176) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_863_2589_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsZeroResidualOne015Pairs : Finset (ℕ × ℕ) :=
  [(863, 2589)].toFinset

theorem PeriodicMainRecordsZeroResidualOne015_value_on_records :
    ∀ p ∈ PeriodicMainRecordsZeroResidualOne015Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsZeroResidualOne015Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_863_2589_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
