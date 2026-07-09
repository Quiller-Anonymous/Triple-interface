import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainSymmetry

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_swap_mem_leftOnlyThree :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs,
      (p.2, p.1) ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rcases p with ⟨q, q'⟩
  have hswap :
      (q', q) ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_swap_mem_leftOnlyThree
      (q, q') hp
  have hleft :
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 (q', q) = 0 :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_value_on_records
      (q', q) hswap
  calc
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (q, q')
        = surrogatePeriodicMainActiveOrderedPairSummandRat X0 (q', q) := by
          exact surrogatePeriodicMainActiveOrderedPairSummandRat_comm X0 q q'
    _ = 0 := hleft

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
