import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem routeADirectCountProbe_block :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 1 = (56 : ℚ) := by
  native_decide

theorem routeADirectCountProbe_pair :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 1 = (48 : ℚ) := by
  native_decide

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
