import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def routeARowPartNativeProbeChunk : Finset ℕ :=
  ([1, 2, 5, 7, 10, 14, 17, 34] : List ℕ).toFinset

theorem routeARowPartNativeProbe :
    (∑ h ∈ routeARowPartNativeProbeChunk,
      ramanujanGcdClassCoeffRat 714 1 * ramanujanGcdClassCoeffRat 1190 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 714 1190) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 714 1190 1 h
                - ramanujanGcdClassWindowAverageRat X0 1190 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 714 1
                - ramanujanGcdClassWindowAverageRat X0 714 1
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 1190 h
                + ramanujanGcdClassWindowAverageRat X0 714 1
                    * ramanujanGcdClassWindowAverageRat X0 1190 h
                    * evenRamanujanBlockCountRat 714 1190))
    ) = (0 : ℚ) / 1 := by
  native_decide

theorem routeATermNativeProbe :
    ramanujanGcdClassCoeffRat 714 1 * ramanujanGcdClassCoeffRat 1190 2
      * ((((H + 1) / centeredRamanujanPairBlockPeriod 714 1190) : ℕ)
          • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 714 1190 1 2
              - ramanujanGcdClassWindowAverageRat X0 1190 2
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 714 1
              - ramanujanGcdClassWindowAverageRat X0 714 1
                  * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 1190 2
              + ramanujanGcdClassWindowAverageRat X0 714 1
                  * ramanujanGcdClassWindowAverageRat X0 1190 2
                  * evenRamanujanBlockCountRat 714 1190))
      = (0 : ℚ) / 1 := by
  native_decide

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
