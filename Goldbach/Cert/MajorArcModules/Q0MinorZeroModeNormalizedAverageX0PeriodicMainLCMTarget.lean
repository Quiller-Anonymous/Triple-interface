import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveDyadicBridge

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Bridge from the LCM-compressed nondyadic surface to the existing nondyadic
target set. The set equality is intentionally supplied as a separate
certificate: proving it monolithically by `native_decide` is too expensive
over the full 27,657-pair target.
-/

theorem periodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic_actual_sum_of_lcm_target_eq
    (hpair_eq :
      PeriodicMainNonDyadicLCMPairs =
        PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic)
    (hzero :
      ∀ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic,
        surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
      PeriodicMainNonDyadicLCMTotal := by
  rw [← hpair_eq]
  exact PeriodicMainNonDyadicLCM_actual_sum (by
    intro p hp
    exact hzero p (by
      simpa [hpair_eq] using hp))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
