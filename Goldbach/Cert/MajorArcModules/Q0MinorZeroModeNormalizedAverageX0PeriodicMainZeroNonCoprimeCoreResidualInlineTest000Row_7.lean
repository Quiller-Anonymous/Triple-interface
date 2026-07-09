import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualInlineTest000Row_7Part0

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem periodicMainPair_7_21_X1000000_divRight_for_row_7 : Nat.divisors 21 = ([1, 3, 7, 21] : List ℕ).toFinset := by
  native_decide

theorem periodicMainPair_7_21_X1000000_row_7 :
    (∑ h ∈ Nat.divisors 21,
      ramanujanGcdClassCoeffRat 7 7 * ramanujanGcdClassCoeffRat 21 h
        * ((((H + 1) / centeredRamanujanPairBlockPeriod 7 21) : ℕ)
            • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 21 7 h
                - ramanujanGcdClassWindowAverageRat X0 21 h
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 7 7
                - ramanujanGcdClassWindowAverageRat X0 7 7
                    * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 21 h
                + ramanujanGcdClassWindowAverageRat X0 7 7
                    * ramanujanGcdClassWindowAverageRat X0 21 h
                    * evenRamanujanBlockCountRat 7 21))
    ) = (0 : ℚ) / 1 := by
  rw [periodicMainPair_7_21_X1000000_divRight_for_row_7]
  have hset : ([1, 3, 7, 21] : List ℕ).toFinset = periodicMainPair_7_21_X1000000_rowChunk_7_0 := by
    native_decide
  rw [hset]
  rw [periodicMainPair_7_21_X1000000_rowPart_7_0]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
