import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc5
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualRightOnlyThreeSwap
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeBaseFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainSymmetry

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
  leftOnlyThree_value_on_records :=
    by
      intro p hp _ _
      exact PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_acc
        p hp
  rightOnlyThree_value_on_records := by
    intro p hp _ _
    rcases p with ⟨q, q'⟩
    have hswap :
        (q', q) ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs :=
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_swap_mem_leftOnlyThree
        (q, q') hp
    have hleft :
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 (q', q) = 0 :=
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records_acc
        (q', q) hswap
    calc
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 (q, q')
          = surrogatePeriodicMainActiveOrderedPairSummandRat X0 (q', q) := by
            exact surrogatePeriodicMainActiveOrderedPairSummandRat_comm X0 q q'
      _ = 0 := hleft
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
