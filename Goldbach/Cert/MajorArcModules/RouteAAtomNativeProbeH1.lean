import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem routeAAtomNativeProbeH1_pair :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 714 1190 1 1 = (0 : ℚ) := by
  native_decide

theorem routeAAtomNativeProbeH1_blockLeft :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 714 1 = (0 : ℚ) := by
  native_decide

theorem routeAAtomNativeProbeH1_blockRight :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 714 1190 1190 1 = (0 : ℚ) := by
  native_decide

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
