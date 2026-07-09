import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem routeASpecialZeroSimplifyProbe :
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
    native_decide
  have hBlockRight : rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 1190 1 = (0 : ℚ) := by
    native_decide
  have hPair : rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 714 1190 1 1 = (0 : ℚ) := by
    native_decide
  rw [hPair, hAvgRight, hBlockRight]
  simp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
