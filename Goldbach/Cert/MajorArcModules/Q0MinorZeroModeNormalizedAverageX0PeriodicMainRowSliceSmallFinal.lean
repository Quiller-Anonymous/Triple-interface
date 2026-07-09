import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceSmall
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceSix

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Small-row periodic-main facts for the row-slice certificate surface.

Rows `[1,2)` and `[2,3)` are already proved in `RowAssembly`.  This module
packages the newly structural rows `[3,4)`, `[4,5)`, and `[6,7)` so downstream
Route A modules can import a stable surface instead of the proof internals.
-/

theorem periodicMainRowSlice002_certified :
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 3 4,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainRowSliceTotal002 :=
  periodicMainRowSlice002_true

theorem periodicMainRowSlice003_certified :
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 4 5,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainRowSliceTotal003 :=
  periodicMainRowSlice003_true

theorem periodicMainRowSlice005_certified :
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 6 7,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainRowSliceTotal005 :=
  periodicMainRowSlice005_true

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
