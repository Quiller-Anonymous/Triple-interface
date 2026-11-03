import Goldbach.Cert.MajorArcModules.Q0MinorRouteAMeanVarianceTargets
import Goldbach.Cert.MajorArcModules.RouteAFixedBankObstruction

/-!
# Route A PSB positive-mean obstruction

This module records the consequence of the fixed-bank counterexample on the exact theorem surface
used by the PSB mean layer.  It prevents the current universal positive-mean target from being
treated as an unfilled certificate obligation.
-/

namespace Goldbach.Cert.MajorArcModules.RouteAPSBMeanObstruction

open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MinorRouteAMeanVarianceTargets
open Goldbach.Cert.MajorArcModules.RouteAFixedBankObstruction

/-- The current exact dyadic mean target cannot carry a positive profile uniformly in `X`. -/
theorem no_uniformly_positive_routeAVisibleDyadicMeanLowerBound :
    ¬ ∃ M : ℕ → ℝ,
        RouteAVisibleDyadicMeanLowerBound M
          ∧ (∀ {X : ℕ}, X0 ≤ X → 0 < M X) := by
  rintro ⟨M, hmean, hpos⟩
  exact no_uniformly_positive_routeVisibleWindowMean ⟨M, hmean.bound, hpos⟩

end Goldbach.Cert.MajorArcModules.RouteAPSBMeanObstruction
