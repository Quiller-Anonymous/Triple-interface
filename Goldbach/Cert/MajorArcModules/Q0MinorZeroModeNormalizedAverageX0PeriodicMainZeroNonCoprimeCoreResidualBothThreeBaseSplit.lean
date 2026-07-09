import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeBaseTransport

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Base-zero split for the `bothThree` residual.

The dyadic transport layer reduces every record to the odd-core base pair
`(3 * bothThreeOddCore p.1, 3 * bothThreeOddCore p.2)`.  This module exposes
the remaining proof obligation in the same coprime-core/non-coprime-core split
used by the structural analysis.
-/

structure PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeBaseCoreSplitCertificateAtX0 :
    Prop where
  coprimeCore_baseFullBlockZero_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs,
      bothThreeBaseFullBlockZeroAtX0 p
  nonCoprimeCore_baseFullBlockZero_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs,
      bothThreeBaseFullBlockZeroAtX0 p

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_baseFullBlockZero_of_baseCoreSplit
    (cert :
      PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeBaseCoreSplitCertificateAtX0) :
    PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeBaseFullBlockZeroCertificateAtX0 where
  baseFullBlockZero_on_records := by
    intro p hp
    rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs_eq_coprimeCore_union_nonCoprimeCore] at hp
    rcases Finset.mem_union.mp hp with hpCop | hpNon
    · exact cert.coprimeCore_baseFullBlockZero_on_records p hpCop
    · exact cert.nonCoprimeCore_baseFullBlockZero_on_records p hpNon

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records_of_baseCoreSplit
    (cert :
      PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeBaseCoreSplitCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records_of_baseFullBlockZero
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_baseFullBlockZero_of_baseCoreSplit
      cert)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
