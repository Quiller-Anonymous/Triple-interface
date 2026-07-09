import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_1
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_2
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_5
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_7
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_10
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_14
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_17
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_34
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_35
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_70
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_85
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_119
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_170
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_238
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_595
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeBigTermSplitStructuralTest519Term_1_1190

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def routeARowPartRewriteProbeChunk : Finset ℕ :=
  ([1, 2, 5, 7, 10, 14, 17, 34, 35, 70, 85, 119, 170, 238, 595, 1190] : List ℕ).toFinset

theorem routeARowPartRewriteProbe :
    (∑ h ∈ routeARowPartRewriteProbeChunk,
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
  norm_num [routeARowPartRewriteProbeChunk,
    periodicMainPair_714_1190_X1000000_term_1_1,
    periodicMainPair_714_1190_X1000000_term_1_2,
    periodicMainPair_714_1190_X1000000_term_1_5,
    periodicMainPair_714_1190_X1000000_term_1_7,
    periodicMainPair_714_1190_X1000000_term_1_10,
    periodicMainPair_714_1190_X1000000_term_1_14,
    periodicMainPair_714_1190_X1000000_term_1_17,
    periodicMainPair_714_1190_X1000000_term_1_34,
    periodicMainPair_714_1190_X1000000_term_1_35,
    periodicMainPair_714_1190_X1000000_term_1_70,
    periodicMainPair_714_1190_X1000000_term_1_85,
    periodicMainPair_714_1190_X1000000_term_1_119,
    periodicMainPair_714_1190_X1000000_term_1_170,
    periodicMainPair_714_1190_X1000000_term_1_238,
    periodicMainPair_714_1190_X1000000_term_1_595,
    periodicMainPair_714_1190_X1000000_term_1_1190]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
