import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalCoverage

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Public wrapper retaining the original final theorem surface. -/

theorem periodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic_actual_sum :
    (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonzeroWithoutRowFiveNonDyadicClassTotal := by
  rw [← PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs_eq_target]
  rw [PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs_actual_sum]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
