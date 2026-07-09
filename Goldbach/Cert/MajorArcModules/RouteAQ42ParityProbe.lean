import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem routeA_probe_avg_42_21_native :
    ramanujanGcdClassWindowAverageRat X0 42 21 = (0 : ℚ) := by
  native_decide

theorem routeA_probe_block_42_146_42_21_rat_zero :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 146 42 21 = (0 : ℚ) := by
  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_zero_of_not_isEven_g_of_isEven_quotient]
  all_goals native_decide

theorem routeA_probe_terms_42_133_14_42_h1_cancel_native :
    (ramanujanGcdClassCoeffRat 42 14 * ramanujanGcdClassCoeffRat 133 1
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 42 133) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 14 1
              - ramanujanGcdClassWindowAverageRat X0 133 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 14
              - ramanujanGcdClassWindowAverageRat X0 42 14
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 133 1
              + ramanujanGcdClassWindowAverageRat X0 42 14
                  * ramanujanGcdClassWindowAverageRat X0 133 1
                  * evenRamanujanBlockCountRat 42 133)))
    + (ramanujanGcdClassCoeffRat 42 42 * ramanujanGcdClassCoeffRat 133 1
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 42 133) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 42 133 42 1
              - ramanujanGcdClassWindowAverageRat X0 133 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 42 42
              - ramanujanGcdClassWindowAverageRat X0 42 42
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 42 133 133 1
              + ramanujanGcdClassWindowAverageRat X0 42 42
                  * ramanujanGcdClassWindowAverageRat X0 133 1
                  * evenRamanujanBlockCountRat 42 133)))
      = (0 : ℚ) := by
  native_decide

theorem routeA_probe_q42_row_reorder (R : ℕ → ℚ) :
    (∑ g ∈ ([1, 2, 3, 6, 7, 14, 21, 42] : List ℕ).toFinset, R g)
      = R 1 + R 3 + R 7 + R 21 + (R 2 + R 6) + (R 14 + R 42) := by
  norm_num [Finset.sum_insert]
  abel

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
