import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroDyadicAssembly
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroRowFive
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveDyadicBaseFinal
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroWithoutRowFiveNonDyadicClassFinal

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Final assembly for the nonzero periodic-main record sum.

This module packages the existing row-five, dyadic, and nondyadic generated
payloads into the single sum fact required by the reduced sparse periodic-main
certificate surface.
-/

noncomputable def periodicMainNonzeroActualValue (p : ℕ × ℕ) : ℚ :=
  surrogatePeriodicMainActiveOrderedPairSummandRat X0 p

theorem periodicMainNonzeroActualValue_on_records :
    ∀ p ∈ PeriodicMainNonzeroRecordPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p =
        periodicMainNonzeroActualValue p := by
  intro p _hp
  rfl

theorem periodicMainNonzeroRecordPairs_actual_sum_eq_cert :
    (∑ p ∈ PeriodicMainNonzeroRecordPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
        surrogatePeriodicMainX0RatCert := by
  refine PeriodicMainNonzeroRecordPairs_sum_eq_cert_of_rowFive_dyadic_and_nondyadic
    PeriodicMainNonzeroRecordPairsRowFive_actual_sum
    periodicMainNonzeroRecordPairsWithoutRowFiveDyadic_actual_sum
    periodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic_actual_sum
    ?_
  native_decide

theorem periodicMainNonzeroActualValue_sum_eq_cert :
    (∑ p ∈ PeriodicMainNonzeroRecordPairs,
      periodicMainNonzeroActualValue p) =
        surrogatePeriodicMainX0RatCert := by
  simpa [periodicMainNonzeroActualValue] using
    periodicMainNonzeroRecordPairs_actual_sum_eq_cert

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
