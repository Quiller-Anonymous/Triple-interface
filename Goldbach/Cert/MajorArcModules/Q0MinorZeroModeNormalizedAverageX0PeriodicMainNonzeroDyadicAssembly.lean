import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroRowFiveBridge
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveDyadicBridge
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainDyadicTransport

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Assembly surface for the compressed nonzero periodic-main route.

The q=5 row is already isolated.  The remaining nonzero records are now split
into the large dyadic slice and the small nondyadic slice.  This wrapper fixes
the theorem shape for the next payloads without committing to whether those
payloads are generated or structural.
-/

theorem PeriodicMainNonzeroRecordPairs_sum_eq_cert_of_rowFive_dyadic_and_nondyadic
    {rowFiveTotal dyadicTotal nondyadicTotal : ℚ}
    (hrow :
      (∑ p ∈ PeriodicMainNonzeroRecordPairsRowFive,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
        rowFiveTotal)
    (hdyadic :
      (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveDyadic,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
          dyadicTotal)
    (hnondyadic :
      (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
          nondyadicTotal)
    (hTotals :
      dyadicTotal + nondyadicTotal + rowFiveTotal =
        surrogatePeriodicMainX0RatCert) :
    (∑ p ∈ PeriodicMainNonzeroRecordPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
        = surrogatePeriodicMainX0RatCert := by
  refine PeriodicMainNonzeroRecordPairs_sum_eq_cert_of_rowFiveAndWithoutRowFiveSum
    hrow ?_
  rw [PeriodicMainNonzeroRecordPairsWithoutRowFive_actual_sum_of_dyadic_and_nondyadic
    hdyadic hnondyadic]
  simpa [add_assoc] using hTotals

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
