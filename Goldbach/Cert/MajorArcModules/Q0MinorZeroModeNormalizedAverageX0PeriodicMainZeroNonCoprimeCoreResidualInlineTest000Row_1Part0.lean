import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def periodicMainPair_7_21_X1000000_rowChunk_1_0 : Finset ℕ :=
  ([1, 3, 7, 21] : List ℕ).toFinset

def periodicMainPair_7_21_X1000000_rowPartValue_1_0 : ℕ → ℚ
| 1 => (-1133786780 : ℚ) / 2778889
| 3 => (1133786780 : ℚ) / 2778889
| 7 => (-6802720680 : ℚ) / 2778889
| 21 => (6802720680 : ℚ) / 2778889
| _ => 0

theorem periodicMainPair_7_21_X1000000_rowPart_1_0 :
    (∑ h ∈ periodicMainPair_7_21_X1000000_rowChunk_1_0,
      ramanujanGcdClassCoeffRat 7 1 * ramanujanGcdClassCoeffRat 21 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 7 21) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 21 1 h
                - ramanujanGcdClassWindowAverageRat X0 21 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 7 1
                - ramanujanGcdClassWindowAverageRat X0 7 1
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 21 h
                + ramanujanGcdClassWindowAverageRat X0 7 1
                    * ramanujanGcdClassWindowAverageRat X0 21 h
                    * evenRamanujanBlockCountRat 7 21))
    ) = (0 : ℚ) / 1 := by
  have hsum :
      (∑ h ∈ periodicMainPair_7_21_X1000000_rowChunk_1_0,
        ramanujanGcdClassCoeffRat 7 1 * ramanujanGcdClassCoeffRat 21 h
          * ((((H + 1) / centeredRamanujanPairBlockPeriod 7 21) : ℕ)
              • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 21 1 h
                  - ramanujanGcdClassWindowAverageRat X0 21 h
                      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 7 1
                  - ramanujanGcdClassWindowAverageRat X0 7 1
                      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 21 h
                  + ramanujanGcdClassWindowAverageRat X0 7 1
                      * ramanujanGcdClassWindowAverageRat X0 21 h
                      * evenRamanujanBlockCountRat 7 21))
      ) = (∑ h ∈ periodicMainPair_7_21_X1000000_rowChunk_1_0, periodicMainPair_7_21_X1000000_rowPartValue_1_0 h) := by
    apply Finset.sum_congr rfl
    intro h hh
    simp [periodicMainPair_7_21_X1000000_rowChunk_1_0] at hh
    rcases hh with rfl | rfl | rfl | rfl
    · have hCoeffLeft : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
        native_decide
      have hCoeffRight : ramanujanGcdClassCoeffRat 21 1 = (1 : ℚ) / 1 := by
        native_decide
      have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
        native_decide
      have hAvgRight : ramanujanGcdClassWindowAverageRat X0 21 1 = (2858 : ℚ) / 5001 := by
        native_decide
      have hBlockLeft : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 7 1 = (18 : ℚ) := by
        rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
        all_goals native_decide
      have hBlockRight : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 21 1 = (12 : ℚ) := by
        rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
        all_goals native_decide
      have hPair : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 21 1 1 = (12 : ℚ) := by
        rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
        · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
          all_goals native_decide
        · norm_num [ramanujanGcdClassJointCompatibility]
      norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
        periodicMainPair_7_21_X1000000_rowPartValue_1_0, hCoeffLeft, hCoeffRight, hAvgLeft, hAvgRight,
        hBlockLeft, hBlockRight, hPair]
    · have hCoeffLeft : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
        native_decide
      have hCoeffRight : ramanujanGcdClassCoeffRat 21 3 = (-2 : ℚ) / 1 := by
        native_decide
      have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
        native_decide
      have hAvgRight : ramanujanGcdClassWindowAverageRat X0 21 3 = (1429 : ℚ) / 5001 := by
        native_decide
      have hBlockLeft : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 7 1 = (18 : ℚ) := by
        rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
        all_goals native_decide
      have hBlockRight : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 21 3 = (6 : ℚ) := by
        rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
        all_goals native_decide
      have hPair : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 21 1 3 = (6 : ℚ) := by
        rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
        · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
          all_goals native_decide
        · norm_num [ramanujanGcdClassJointCompatibility]
      norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
        periodicMainPair_7_21_X1000000_rowPartValue_1_0, hCoeffLeft, hCoeffRight, hAvgLeft, hAvgRight,
        hBlockLeft, hBlockRight, hPair]
    · have hCoeffLeft : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
        native_decide
      have hCoeffRight : ramanujanGcdClassCoeffRat 21 7 = (-6 : ℚ) / 1 := by
        native_decide
      have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
        native_decide
      have hAvgRight : ramanujanGcdClassWindowAverageRat X0 21 7 = (476 : ℚ) / 5001 := by
        native_decide
      have hBlockLeft : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 7 1 = (18 : ℚ) := by
        rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
        all_goals native_decide
      have hBlockRight : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 21 7 = (2 : ℚ) := by
        rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
        all_goals native_decide
      have hPair : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 21 1 7 = (0 : ℚ) := by
        rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
        norm_num [ramanujanGcdClassJointCompatibility]
      norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
        periodicMainPair_7_21_X1000000_rowPartValue_1_0, hCoeffLeft, hCoeffRight, hAvgLeft, hAvgRight,
        hBlockLeft, hBlockRight, hPair]
    · have hCoeffLeft : ramanujanGcdClassCoeffRat 7 1 = (-1 : ℚ) / 1 := by
        native_decide
      have hCoeffRight : ramanujanGcdClassCoeffRat 21 21 = (12 : ℚ) / 1 := by
        native_decide
      have hAvgLeft : ramanujanGcdClassWindowAverageRat X0 7 1 = (1429 : ℚ) / 1667 := by
        native_decide
      have hAvgRight : ramanujanGcdClassWindowAverageRat X0 21 21 = (238 : ℚ) / 5001 := by
        native_decide
      have hBlockLeft : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 7 1 = (18 : ℚ) := by
        rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
        all_goals native_decide
      have hBlockRight : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 21 21 = (1 : ℚ) := by
        rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
        all_goals native_decide
      have hPair : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 21 1 21 = (0 : ℚ) := by
        rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_zero_of_incompatible]
        norm_num [ramanujanGcdClassJointCompatibility]
      norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
        periodicMainPair_7_21_X1000000_rowPartValue_1_0, hCoeffLeft, hCoeffRight, hAvgLeft, hAvgRight,
        hBlockLeft, hBlockRight, hPair]
  rw [hsum]
  norm_num [periodicMainPair_7_21_X1000000_rowChunk_1_0, periodicMainPair_7_21_X1000000_rowPartValue_1_0]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
