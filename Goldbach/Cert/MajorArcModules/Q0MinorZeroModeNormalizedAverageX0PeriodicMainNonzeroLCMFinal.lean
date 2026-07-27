import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMReverseTarget

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
LCM-based final wrapper for the non-dyadic/non-row-five periodic-main block.

The LCM payload certifies the non-dyadic/non-row-five mean-product sum.  The
only remaining arithmetic obligation is the pointwise vanishing of the three
aggregate components on that target set.
-/

theorem periodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic_actual_sum_lcm
    (hzero :
      ∀ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic,
        surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
        = PeriodicMainNonDyadicLCMTotal := by
  exact periodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic_actual_sum_of_lcm_target hzero

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
