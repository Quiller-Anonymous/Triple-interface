import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualRightOnlyThreeFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeBaseFinal

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Final assembly for the non-coprime dyadic core residual zero certificate.

The residual is split by divisibility by `3` on the two coordinates.  The
left-only and right-only surfaces are generated/value certificates; the
both-three surface is the structural base-core certificate.
-/

theorem PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0_certified :
    PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0 where
  leftOnlyThree_value_on_records := by
    intro p hp _ _
    exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records
        p hp
  rightOnlyThree_value_on_records := by
    intro p hp _ _
    exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_value_on_records
        p hp
  bothThree_value_on_records := by
    intro p hp _ _
    exact
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records_certified
        p hp

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidual_value_on_records_certified :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidual_value_on_records_of_divisibility
    PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0_certified

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
