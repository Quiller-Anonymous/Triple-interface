import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidual

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_swap_mem_leftOnlyThree :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs,
      (p.2, p.1) ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs := by
  native_decide

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
