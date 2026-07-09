import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem routeAStructuralRatZeroProbe :
    ramanujanGcdClassCoeffRat 714 1 * ramanujanGcdClassCoeffRat 1190 1
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 714 1190) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 714 1190 1 1
              - ramanujanGcdClassWindowAverageRat X0 1190 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 714 1
              - ramanujanGcdClassWindowAverageRat X0 714 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 1190 1
              + ramanujanGcdClassWindowAverageRat X0 714 1
                  * ramanujanGcdClassWindowAverageRat X0 1190 1
                  * evenRamanujanBlockCountRat 714 1190))
      = (0 : ℚ) / 1 := by
  have hAvgRight : ramanujanGcdClassWindowAverageRat X0 1190 1 = (0 : ℚ) / 1 := by
    have hreal : ramanujanGcdClassWindowAverage X0 1190 1 = 0 := by
      exact ramanujanGcdClassWindowAverage_eq_zero_of_isEven_q_of_not_isEven_g
        (by native_decide) (by native_decide)
    have hcast : (ramanujanGcdClassWindowAverageRat X0 1190 1 : ℝ) = 0 := by
      rw [← ramanujanGcdClassWindowAverage_eq_ratCast X0 1190 1]
      exact hreal
    norm_num at hcast ⊢
    exact Rat.cast_inj.mp hcast
  have hBlockRight : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 1190 1 = (0 : ℚ) := by
    have hreal :
        rawEvenRamanujanGcdClassBlockPeriodicCount X0 714 1190 1190 1 = 0 := by
      exact rawEvenRamanujanGcdClassBlockPeriodicCount_eq_zero_of_not_isEven_g_of_isEven_quotient
        X0 714 1190 1190 1 (by native_decide) (by native_decide)
    have hcast :
        (rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 1190 1 : ℝ) = 0 := by
      rw [← rawEvenRamanujanGcdClassBlockPeriodicCount_eq_ratCast X0 714 1190 1190 1]
      exact hreal
    norm_num at hcast ⊢
    exact Rat.cast_inj.mp hcast
  have hPair : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 714 1190 1 1 = (0 : ℚ) := by
    have hPeriodic :
        rawEvenRamanujanGcdClassPairBlockPeriodicCount X0 714 1190 1 1 = 0 := by
      exact rawEvenRamanujanGcdClassPairBlockPeriodicCount_eq_zero_of_not_isEven_lcm_of_isEven_jointModulus
        X0 714 1190 1 1 (by native_decide) (by native_decide)
    have hreal :
        rawEvenRamanujanGcdClassPairBlockResolvedCount X0 714 1190 1 1 = 0 := by
      unfold rawEvenRamanujanGcdClassPairBlockResolvedCount
      by_cases hcompat : ramanujanGcdClassJointCompatibility 714 1190 1 1
      · simp [hcompat, hPeriodic]
      · simp [hcompat]
    have hcast :
        (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 714 1190 1 1 : ℝ) = 0 := by
      rw [← rawEvenRamanujanGcdClassPairBlockResolvedCount_eq_ratCast X0 714 1190 1 1]
      exact hreal
    norm_num at hcast ⊢
    exact Rat.cast_inj.mp hcast
  rw [hPair, hAvgRight, hBlockRight]
  simp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
