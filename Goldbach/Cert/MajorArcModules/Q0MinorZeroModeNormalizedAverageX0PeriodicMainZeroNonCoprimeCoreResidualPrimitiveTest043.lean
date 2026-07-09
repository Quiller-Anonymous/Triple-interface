import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main zero-record proofs for selected JSON indices [43,44). -/

theorem periodicMainPair_15_21_X1000000_divLeft : Nat.divisors 15 = ([1, 3, 5, 15] : List ℕ).toFinset := by
  decide

theorem periodicMainPair_15_21_X1000000_divRight : Nat.divisors 21 = ([1, 3, 7, 21] : List ℕ).toFinset := by
  decide

theorem periodicMainPair_15_21_X1000000_coeffLeft_1 : ramanujanGcdClassCoeffRat 15 1 = (1 : ℚ) / 1 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_coeffLeft_3 : ramanujanGcdClassCoeffRat 15 3 = (-2 : ℚ) / 1 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_coeffLeft_5 : ramanujanGcdClassCoeffRat 15 5 = (-4 : ℚ) / 1 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_coeffLeft_15 : ramanujanGcdClassCoeffRat 15 15 = (8 : ℚ) / 1 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_coeffRight_1 : ramanujanGcdClassCoeffRat 21 1 = (1 : ℚ) / 1 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_coeffRight_3 : ramanujanGcdClassCoeffRat 21 3 = (-2 : ℚ) / 1 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_coeffRight_7 : ramanujanGcdClassCoeffRat 21 7 = (-6 : ℚ) / 1 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_coeffRight_21 : ramanujanGcdClassCoeffRat 21 21 = (12 : ℚ) / 1 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_avgLeft_1 : ramanujanGcdClassWindowAverageRat X0 15 1 = (2666 : ℚ) / 5001 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_avgLeft_3 : ramanujanGcdClassWindowAverageRat X0 15 3 = (1334 : ℚ) / 5001 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_avgLeft_5 : ramanujanGcdClassWindowAverageRat X0 15 5 = (668 : ℚ) / 5001 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_avgLeft_15 : ramanujanGcdClassWindowAverageRat X0 15 15 = (111 : ℚ) / 1667 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_avgRight_1 : ramanujanGcdClassWindowAverageRat X0 21 1 = (2858 : ℚ) / 5001 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_avgRight_3 : ramanujanGcdClassWindowAverageRat X0 21 3 = (1429 : ℚ) / 5001 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_avgRight_7 : ramanujanGcdClassWindowAverageRat X0 21 7 = (476 : ℚ) / 5001 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_avgRight_21 : ramanujanGcdClassWindowAverageRat X0 21 21 = (238 : ℚ) / 5001 := by
  native_decide

theorem periodicMainPair_15_21_X1000000_blockLeft_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 1 = (56 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_blockLeft_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 3 = (28 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_blockLeft_5 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 5 = (14 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_blockLeft_15 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 15 = (7 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_blockRight_1 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 1 = (60 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_blockRight_3 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 3 = (30 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_blockRight_7 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 7 = (10 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_blockRight_21 : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 21 = (5 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_1_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 1 = (48 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_1_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 3 = (0 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_1_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 7 = (8 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_1_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 21 = (0 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_3_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 3 1 = (0 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_3_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 3 3 = (24 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_3_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 3 7 = (0 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_3_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 3 21 = (4 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_5_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 5 1 = (12 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_5_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 5 3 = (0 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_5_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 5 7 = (2 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_5_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 5 21 = (0 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_15_1 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 15 1 = (0 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_15_3 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 15 3 = (6 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_15_7 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 15 7 = (0 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_pair_15_21 : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 15 21 = (1 : ℚ) := by
  native_decide

theorem periodicMainPair_15_21_X1000000_term_1_1 :
    ramanujanGcdClassCoeffRat 15 1 * ramanujanGcdClassCoeffRat 21 1
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 1
              - ramanujanGcdClassWindowAverageRat X0 21 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 1
              - ramanujanGcdClassWindowAverageRat X0 15 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 1
              + ramanujanGcdClassWindowAverageRat X0 15 1
                  * ramanujanGcdClassWindowAverageRat X0 21 1
                  * evenRamanujanBlockCountRat 15 21))
      = (2089724340 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_1, periodicMainPair_15_21_X1000000_coeffRight_1, periodicMainPair_15_21_X1000000_avgLeft_1, periodicMainPair_15_21_X1000000_avgRight_1,
    periodicMainPair_15_21_X1000000_blockLeft_1, periodicMainPair_15_21_X1000000_blockRight_1, periodicMainPair_15_21_X1000000_pair_1_1]

theorem periodicMainPair_15_21_X1000000_term_1_3 :
    ramanujanGcdClassCoeffRat 15 1 * ramanujanGcdClassCoeffRat 21 3
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 3
              - ramanujanGcdClassWindowAverageRat X0 21 3
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 1
              - ramanujanGcdClassWindowAverageRat X0 15 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 3
              + ramanujanGcdClassWindowAverageRat X0 15 1
                  * ramanujanGcdClassWindowAverageRat X0 21 3
                  * evenRamanujanBlockCountRat 15 21))
      = (4179449244 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_1, periodicMainPair_15_21_X1000000_coeffRight_3, periodicMainPair_15_21_X1000000_avgLeft_1, periodicMainPair_15_21_X1000000_avgRight_3,
    periodicMainPair_15_21_X1000000_blockLeft_1, periodicMainPair_15_21_X1000000_blockRight_3, periodicMainPair_15_21_X1000000_pair_1_3]

theorem periodicMainPair_15_21_X1000000_term_1_7 :
    ramanujanGcdClassCoeffRat 15 1 * ramanujanGcdClassCoeffRat 21 7
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 7
              - ramanujanGcdClassWindowAverageRat X0 21 7
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 1
              - ramanujanGcdClassWindowAverageRat X0 15 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 7
              + ramanujanGcdClassWindowAverageRat X0 15 1
                  * ramanujanGcdClassWindowAverageRat X0 21 7
                  * evenRamanujanBlockCountRat 15 21))
      = (-2089725656 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_1, periodicMainPair_15_21_X1000000_coeffRight_7, periodicMainPair_15_21_X1000000_avgLeft_1, periodicMainPair_15_21_X1000000_avgRight_7,
    periodicMainPair_15_21_X1000000_blockLeft_1, periodicMainPair_15_21_X1000000_blockRight_7, periodicMainPair_15_21_X1000000_pair_1_7]

theorem periodicMainPair_15_21_X1000000_term_1_21 :
    ramanujanGcdClassCoeffRat 15 1 * ramanujanGcdClassCoeffRat 21 21
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 21
              - ramanujanGcdClassWindowAverageRat X0 21 21
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 1
              - ramanujanGcdClassWindowAverageRat X0 15 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 21
              + ramanujanGcdClassWindowAverageRat X0 15 1
                  * ramanujanGcdClassWindowAverageRat X0 21 21
                  * evenRamanujanBlockCountRat 15 21))
      = (-4179447928 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_1, periodicMainPair_15_21_X1000000_coeffRight_21, periodicMainPair_15_21_X1000000_avgLeft_1, periodicMainPair_15_21_X1000000_avgRight_21,
    periodicMainPair_15_21_X1000000_blockLeft_1, periodicMainPair_15_21_X1000000_blockRight_21, periodicMainPair_15_21_X1000000_pair_1_21]

theorem periodicMainPair_15_21_X1000000_term_3_1 :
    ramanujanGcdClassCoeffRat 15 3 * ramanujanGcdClassCoeffRat 21 1
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 3 1
              - ramanujanGcdClassWindowAverageRat X0 21 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 3
              - ramanujanGcdClassWindowAverageRat X0 15 3
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 1
              + ramanujanGcdClassWindowAverageRat X0 15 3
                  * ramanujanGcdClassWindowAverageRat X0 21 1
                  * evenRamanujanBlockCountRat 15 21))
      = (12538346792 : ℚ) / 8336667 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_3, periodicMainPair_15_21_X1000000_coeffRight_1, periodicMainPair_15_21_X1000000_avgLeft_3, periodicMainPair_15_21_X1000000_avgRight_1,
    periodicMainPair_15_21_X1000000_blockLeft_3, periodicMainPair_15_21_X1000000_blockRight_1, periodicMainPair_15_21_X1000000_pair_3_1]

theorem periodicMainPair_15_21_X1000000_term_3_3 :
    ramanujanGcdClassCoeffRat 15 3 * ramanujanGcdClassCoeffRat 21 3
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 3 3
              - ramanujanGcdClassWindowAverageRat X0 21 3
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 3
              - ramanujanGcdClassWindowAverageRat X0 15 3
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 3
              + ramanujanGcdClassWindowAverageRat X0 15 3
                  * ramanujanGcdClassWindowAverageRat X0 21 3
                  * evenRamanujanBlockCountRat 15 21))
      = (25076694712 : ℚ) / 8336667 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_3, periodicMainPair_15_21_X1000000_coeffRight_3, periodicMainPair_15_21_X1000000_avgLeft_3, periodicMainPair_15_21_X1000000_avgRight_3,
    periodicMainPair_15_21_X1000000_blockLeft_3, periodicMainPair_15_21_X1000000_blockRight_3, periodicMainPair_15_21_X1000000_pair_3_3]

theorem periodicMainPair_15_21_X1000000_term_3_7 :
    ramanujanGcdClassCoeffRat 15 3 * ramanujanGcdClassCoeffRat 21 7
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 3 7
              - ramanujanGcdClassWindowAverageRat X0 21 7
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 3
              - ramanujanGcdClassWindowAverageRat X0 15 3
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 7
              + ramanujanGcdClassWindowAverageRat X0 15 3
                  * ramanujanGcdClassWindowAverageRat X0 21 7
                  * evenRamanujanBlockCountRat 15 21))
      = (-4179449808 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_3, periodicMainPair_15_21_X1000000_coeffRight_7, periodicMainPair_15_21_X1000000_avgLeft_3, periodicMainPair_15_21_X1000000_avgRight_7,
    periodicMainPair_15_21_X1000000_blockLeft_3, periodicMainPair_15_21_X1000000_blockRight_7, periodicMainPair_15_21_X1000000_pair_3_7]

theorem periodicMainPair_15_21_X1000000_term_3_21 :
    ramanujanGcdClassCoeffRat 15 3 * ramanujanGcdClassCoeffRat 21 21
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 3 21
              - ramanujanGcdClassWindowAverageRat X0 21 21
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 3
              - ramanujanGcdClassWindowAverageRat X0 15 3
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 21
              + ramanujanGcdClassWindowAverageRat X0 15 3
                  * ramanujanGcdClassWindowAverageRat X0 21 21
                  * evenRamanujanBlockCountRat 15 21))
      = (-8358897360 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_3, periodicMainPair_15_21_X1000000_coeffRight_21, periodicMainPair_15_21_X1000000_avgLeft_3, periodicMainPair_15_21_X1000000_avgRight_21,
    periodicMainPair_15_21_X1000000_blockLeft_3, periodicMainPair_15_21_X1000000_blockRight_21, periodicMainPair_15_21_X1000000_pair_3_21]

theorem periodicMainPair_15_21_X1000000_term_5_1 :
    ramanujanGcdClassCoeffRat 15 5 * ramanujanGcdClassCoeffRat 21 1
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 5 1
              - ramanujanGcdClassWindowAverageRat X0 21 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 5
              - ramanujanGcdClassWindowAverageRat X0 15 5
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 1
              + ramanujanGcdClassWindowAverageRat X0 15 5
                  * ramanujanGcdClassWindowAverageRat X0 21 1
                  * evenRamanujanBlockCountRat 15 21))
      = (-2089725280 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_5, periodicMainPair_15_21_X1000000_coeffRight_1, periodicMainPair_15_21_X1000000_avgLeft_5, periodicMainPair_15_21_X1000000_avgRight_1,
    periodicMainPair_15_21_X1000000_blockLeft_5, periodicMainPair_15_21_X1000000_blockRight_1, periodicMainPair_15_21_X1000000_pair_5_1]

theorem periodicMainPair_15_21_X1000000_term_5_3 :
    ramanujanGcdClassCoeffRat 15 5 * ramanujanGcdClassCoeffRat 21 3
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 5 3
              - ramanujanGcdClassWindowAverageRat X0 21 3
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 5
              - ramanujanGcdClassWindowAverageRat X0 15 5
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 3
              + ramanujanGcdClassWindowAverageRat X0 15 5
                  * ramanujanGcdClassWindowAverageRat X0 21 3
                  * evenRamanujanBlockCountRat 15 21))
      = (-4179448304 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_5, periodicMainPair_15_21_X1000000_coeffRight_3, periodicMainPair_15_21_X1000000_avgLeft_5, periodicMainPair_15_21_X1000000_avgRight_3,
    periodicMainPair_15_21_X1000000_blockLeft_5, periodicMainPair_15_21_X1000000_blockRight_3, periodicMainPair_15_21_X1000000_pair_5_3]

theorem periodicMainPair_15_21_X1000000_term_5_7 :
    ramanujanGcdClassCoeffRat 15 5 * ramanujanGcdClassCoeffRat 21 7
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 5 7
              - ramanujanGcdClassWindowAverageRat X0 21 7
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 5
              - ramanujanGcdClassWindowAverageRat X0 15 5
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 7
              + ramanujanGcdClassWindowAverageRat X0 15 5
                  * ramanujanGcdClassWindowAverageRat X0 21 7
                  * evenRamanujanBlockCountRat 15 21))
      = (2089720016 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_5, periodicMainPair_15_21_X1000000_coeffRight_7, periodicMainPair_15_21_X1000000_avgLeft_5, periodicMainPair_15_21_X1000000_avgRight_7,
    periodicMainPair_15_21_X1000000_blockLeft_5, periodicMainPair_15_21_X1000000_blockRight_7, periodicMainPair_15_21_X1000000_pair_5_7]

theorem periodicMainPair_15_21_X1000000_term_5_21 :
    ramanujanGcdClassCoeffRat 15 5 * ramanujanGcdClassCoeffRat 21 21
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 5 21
              - ramanujanGcdClassWindowAverageRat X0 21 21
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 5
              - ramanujanGcdClassWindowAverageRat X0 15 5
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 21
              + ramanujanGcdClassWindowAverageRat X0 15 5
                  * ramanujanGcdClassWindowAverageRat X0 21 21
                  * evenRamanujanBlockCountRat 15 21))
      = (4179453568 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_5, periodicMainPair_15_21_X1000000_coeffRight_21, periodicMainPair_15_21_X1000000_avgLeft_5, periodicMainPair_15_21_X1000000_avgRight_21,
    periodicMainPair_15_21_X1000000_blockLeft_5, periodicMainPair_15_21_X1000000_blockRight_21, periodicMainPair_15_21_X1000000_pair_5_21]

theorem periodicMainPair_15_21_X1000000_term_15_1 :
    ramanujanGcdClassCoeffRat 15 15 * ramanujanGcdClassCoeffRat 21 1
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 15 1
              - ramanujanGcdClassWindowAverageRat X0 21 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 15
              - ramanujanGcdClassWindowAverageRat X0 15 15
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 1
              + ramanujanGcdClassWindowAverageRat X0 15 15
                  * ramanujanGcdClassWindowAverageRat X0 21 1
                  * evenRamanujanBlockCountRat 15 21))
      = (-12538348672 : ℚ) / 8336667 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_15, periodicMainPair_15_21_X1000000_coeffRight_1, periodicMainPair_15_21_X1000000_avgLeft_15, periodicMainPair_15_21_X1000000_avgRight_1,
    periodicMainPair_15_21_X1000000_blockLeft_15, periodicMainPair_15_21_X1000000_blockRight_1, periodicMainPair_15_21_X1000000_pair_15_1]

theorem periodicMainPair_15_21_X1000000_term_15_3 :
    ramanujanGcdClassCoeffRat 15 15 * ramanujanGcdClassCoeffRat 21 3
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 15 3
              - ramanujanGcdClassWindowAverageRat X0 21 3
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 15
              - ramanujanGcdClassWindowAverageRat X0 15 15
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 3
              + ramanujanGcdClassWindowAverageRat X0 15 15
                  * ramanujanGcdClassWindowAverageRat X0 21 3
                  * evenRamanujanBlockCountRat 15 21))
      = (-25076692832 : ℚ) / 8336667 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_15, periodicMainPair_15_21_X1000000_coeffRight_3, periodicMainPair_15_21_X1000000_avgLeft_15, periodicMainPair_15_21_X1000000_avgRight_3,
    periodicMainPair_15_21_X1000000_blockLeft_15, periodicMainPair_15_21_X1000000_blockRight_3, periodicMainPair_15_21_X1000000_pair_15_3]

theorem periodicMainPair_15_21_X1000000_term_15_7 :
    ramanujanGcdClassCoeffRat 15 15 * ramanujanGcdClassCoeffRat 21 7
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 15 7
              - ramanujanGcdClassWindowAverageRat X0 21 7
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 15
              - ramanujanGcdClassWindowAverageRat X0 15 15
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 7
              + ramanujanGcdClassWindowAverageRat X0 15 15
                  * ramanujanGcdClassWindowAverageRat X0 21 7
                  * evenRamanujanBlockCountRat 15 21))
      = (4179446048 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_15, periodicMainPair_15_21_X1000000_coeffRight_7, periodicMainPair_15_21_X1000000_avgLeft_15, periodicMainPair_15_21_X1000000_avgRight_7,
    periodicMainPair_15_21_X1000000_blockLeft_15, periodicMainPair_15_21_X1000000_blockRight_7, periodicMainPair_15_21_X1000000_pair_15_7]

theorem periodicMainPair_15_21_X1000000_term_15_21 :
    ramanujanGcdClassCoeffRat 15 15 * ramanujanGcdClassCoeffRat 21 21
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 15 21
              - ramanujanGcdClassWindowAverageRat X0 21 21
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 15
              - ramanujanGcdClassWindowAverageRat X0 15 15
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 21
              + ramanujanGcdClassWindowAverageRat X0 15 15
                  * ramanujanGcdClassWindowAverageRat X0 21 21
                  * evenRamanujanBlockCountRat 15 21))
      = (8358901120 : ℚ) / 2778889 := by
  norm_num [H, centeredRamanujanPairBlockPeriod, evenRamanujanBlockCountRat,
    periodicMainPair_15_21_X1000000_coeffLeft_15, periodicMainPair_15_21_X1000000_coeffRight_21, periodicMainPair_15_21_X1000000_avgLeft_15, periodicMainPair_15_21_X1000000_avgRight_21,
    periodicMainPair_15_21_X1000000_blockLeft_15, periodicMainPair_15_21_X1000000_blockRight_21, periodicMainPair_15_21_X1000000_pair_15_21]

theorem periodicMainPair_15_21_X1000000_row_1 :
    (∑ h ∈ Nat.divisors 21,
      ramanujanGcdClassCoeffRat 15 1 * ramanujanGcdClassCoeffRat 21 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 h
                - ramanujanGcdClassWindowAverageRat X0 21 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 1
                - ramanujanGcdClassWindowAverageRat X0 15 1
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 h
                + ramanujanGcdClassWindowAverageRat X0 15 1
                    * ramanujanGcdClassWindowAverageRat X0 21 h
                    * evenRamanujanBlockCountRat 15 21))
    ) = (0 : ℚ) / 1 := by
  norm_num [periodicMainPair_15_21_X1000000_divRight, periodicMainPair_15_21_X1000000_term_1_1, periodicMainPair_15_21_X1000000_term_1_3, periodicMainPair_15_21_X1000000_term_1_7, periodicMainPair_15_21_X1000000_term_1_21]

theorem periodicMainPair_15_21_X1000000_row_3 :
    (∑ h ∈ Nat.divisors 21,
      ramanujanGcdClassCoeffRat 15 3 * ramanujanGcdClassCoeffRat 21 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 3 h
                - ramanujanGcdClassWindowAverageRat X0 21 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 3
                - ramanujanGcdClassWindowAverageRat X0 15 3
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 h
                + ramanujanGcdClassWindowAverageRat X0 15 3
                    * ramanujanGcdClassWindowAverageRat X0 21 h
                    * evenRamanujanBlockCountRat 15 21))
    ) = (0 : ℚ) / 1 := by
  norm_num [periodicMainPair_15_21_X1000000_divRight, periodicMainPair_15_21_X1000000_term_3_1, periodicMainPair_15_21_X1000000_term_3_3, periodicMainPair_15_21_X1000000_term_3_7, periodicMainPair_15_21_X1000000_term_3_21]

theorem periodicMainPair_15_21_X1000000_row_5 :
    (∑ h ∈ Nat.divisors 21,
      ramanujanGcdClassCoeffRat 15 5 * ramanujanGcdClassCoeffRat 21 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 5 h
                - ramanujanGcdClassWindowAverageRat X0 21 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 5
                - ramanujanGcdClassWindowAverageRat X0 15 5
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 h
                + ramanujanGcdClassWindowAverageRat X0 15 5
                    * ramanujanGcdClassWindowAverageRat X0 21 h
                    * evenRamanujanBlockCountRat 15 21))
    ) = (0 : ℚ) / 1 := by
  norm_num [periodicMainPair_15_21_X1000000_divRight, periodicMainPair_15_21_X1000000_term_5_1, periodicMainPair_15_21_X1000000_term_5_3, periodicMainPair_15_21_X1000000_term_5_7, periodicMainPair_15_21_X1000000_term_5_21]

theorem periodicMainPair_15_21_X1000000_row_15 :
    (∑ h ∈ Nat.divisors 21,
      ramanujanGcdClassCoeffRat 15 15 * ramanujanGcdClassCoeffRat 21 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 15 21) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 15 h
                - ramanujanGcdClassWindowAverageRat X0 21 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 15
                - ramanujanGcdClassWindowAverageRat X0 15 15
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 21 h
                + ramanujanGcdClassWindowAverageRat X0 15 15
                    * ramanujanGcdClassWindowAverageRat X0 21 h
                    * evenRamanujanBlockCountRat 15 21))
    ) = (0 : ℚ) / 1 := by
  norm_num [periodicMainPair_15_21_X1000000_divRight, periodicMainPair_15_21_X1000000_term_15_1, periodicMainPair_15_21_X1000000_term_15_3, periodicMainPair_15_21_X1000000_term_15_7, periodicMainPair_15_21_X1000000_term_15_21]

theorem periodicMainPair_15_21_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 15 21 = (0 : ℚ) / 1 := by
  unfold centeredRamanujanPairPeriodicMainTermRat
  norm_num [periodicMainPair_15_21_X1000000_divLeft, periodicMainPair_15_21_X1000000_divRight, periodicMainPair_15_21_X1000000_row_1, periodicMainPair_15_21_X1000000_row_3, periodicMainPair_15_21_X1000000_row_5, periodicMainPair_15_21_X1000000_row_15]

theorem periodicMainPair_15_21_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 15 21) = (0 : ℚ) / 1 := by
  have hneq : 15 ≠ 21 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 15 = (5 : ℚ) / 64 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 21 = (5 : ℚ) / 144 := by
    native_decide
  have hvalue : ((5 : ℚ) / 64) * ((5 : ℚ) / 144) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_15_21_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsPrimitiveTest043Pairs : Finset (ℕ × ℕ) :=
  [(15, 21)].toFinset

theorem PeriodicMainRecordsPrimitiveTest043_value_on_records :
    ∀ p ∈ PeriodicMainRecordsPrimitiveTest043Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsPrimitiveTest043Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_15_21_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
