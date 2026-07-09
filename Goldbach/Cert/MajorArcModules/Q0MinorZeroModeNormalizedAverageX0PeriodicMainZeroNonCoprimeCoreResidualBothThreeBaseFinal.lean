import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeAverageValues
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreBase

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Final base-split certificate for the `bothThree` core residual.

The coprime-core side is discharged by the structural raw-core theorem plus the
21 average-value facts.  The non-coprime-core side is discharged by the
deduplicated raw-core chunks plus the same average-value facts.
-/

theorem bothThreeBaseCoreSplitCert_true :
    PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeBaseCoreSplitCertificateAtX0 where
  coprimeCore_baseFullBlockZero_on_records := by
    intro p hp
    exact bothThreeBaseFullBlockZeroAtX0_of_coprimeCore_mem_certified hp
  nonCoprimeCore_baseFullBlockZero_on_records := by
    intro p hp
    exact bothThreeBaseFullBlockZeroAtX0_of_nonCoprimeCore_mem_certified hp

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records_certified :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records_of_baseCoreSplit
    bothThreeBaseCoreSplitCert_true

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
