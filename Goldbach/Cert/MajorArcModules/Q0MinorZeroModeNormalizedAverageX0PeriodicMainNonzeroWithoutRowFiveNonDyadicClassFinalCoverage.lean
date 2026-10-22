import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinalSummary

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Isolate the finite target-set equality from the actual-sum assembly. -/

theorem PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs_eq_target :
    PeriodicMainNonzeroWithoutRowFiveNonDyadicClassPairs = PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic := by
  native_decide

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
