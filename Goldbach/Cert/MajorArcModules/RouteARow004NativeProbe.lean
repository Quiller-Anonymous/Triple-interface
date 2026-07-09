import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowAssembly

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem routeA_row004_native_probe :
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 5 6,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainRowSliceTotal004 := by
  native_decide

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
