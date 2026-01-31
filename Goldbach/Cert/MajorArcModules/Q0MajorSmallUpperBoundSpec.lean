import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
import Goldbach.Cert.MajorArcModules.Q0MajorRoute

/-!
Upper-bound interface for the ε₂-small (small-β) certificate route.

This mirrors the ε₂-large TT* pattern:
- an analytic payload produces a *numerical* upper bound `U` for the small-β deviation quantity;
- a generator emits `U : ℚ` and the advertised budget `εs : ℚ`;
- Lean checks `U ≤ εs`, and downstream code only depends on `Q0MajorSmallBound Δ εs`.

At the current stage, this file is just the interface/seam; it does not implement the analytic
bound.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec

open scoped Interval

open Complex

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorRoute
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcModules.CorrModel

noncomputable section

/--
Certificate-facing analytic payload: a uniform upper bound `U` for the small-β deviation.

This is strictly weaker data than `Q0MajorSmallBound Δ εs`, because it does not mention `εs` at
all; it only produces an upper bound `U` that can later be compared to the budget by a ℚ check.
-/
structure Q0MajorSmallUpperBound (Δ U : ℝ) : Prop where
  nonneg : 0 ≤ U
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ‖Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ - CorrModel.corrModel X N‖ ≤ U

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec
