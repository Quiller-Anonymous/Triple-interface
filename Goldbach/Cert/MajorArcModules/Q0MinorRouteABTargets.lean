import Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

/-!
Thin Route A / Route B integration layer for Vaughan's bridge.

This file deliberately sits *after* the bridge packet. It does not revisit the zero-mode
provenance ladder. Instead it exposes the smallest downstream theorem surfaces that Route A / B
should consume:

* `RouteATarget`: the structured handled model is split into its geometric and zero-mode-shape
  pieces.
* `RouteBTarget`: the canonical minor residual is exactly the sum of those two handled pieces and
  the post-model residual.
* `FinalRouteABClosureTarget`: Route A/B targets plus the residual-energy target.

The point is to keep Vaughan's bridge sealed. Downstream route files should consume these thin
targets, not lower-level details from `Q0MinorZeroModeEnvelope`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorRouteABTargets

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
Thin Route A target: the structured handled model already splits into the geometric part and the
zero-mode-shape part.
-/
structure RouteATarget (κ : ℝ) : Prop where
  handled_split :
    ∀ X N,
      routeHandledModelAtScalar κ X N
        =
      routeHandledGeometricPart X N + routeHandledZeroModeShapePart κ X N

/--
Thin Route B target: the canonical minor residual is exactly the sum of the two handled pieces and
the post-model residual.
-/
structure RouteBTarget (κ : ℝ) : Prop where
  minor_decompose :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        minorResidual X N Δ_canon
          =
        routeHandledGeometricPart X N
          + routeHandledZeroModeShapePart κ X N
          + routeVisibleResidualOfHalfMassScalar κ X N

theorem routeATarget_of_routeABConsumptionTarget
    {κ : ℝ} (_h : RouteABConsumptionTarget κ) :
    RouteATarget κ := by
  refine ⟨?_⟩
  intro X N
  exact routeHandledModelAtScalar_eq_geometric_plus_zeroModeShape κ X N

theorem routeBTarget_of_routeABConsumptionTarget
    {κ : ℝ} (h : RouteABConsumptionTarget κ) :
    RouteBTarget κ := by
  refine ⟨?_⟩
  intro X N hX hN
  exact h.decompose hX hN

/--
Final thin route-integration packet: downstream Route A/B consumers see only their own main-term
targets plus the residual-energy target.
-/
structure FinalRouteABClosureTarget (κ C2 C3 : ℝ) : Prop where
  routeA_target : RouteATarget κ
  routeB_target : RouteBTarget κ
  residual_target : RouteVisibleResidualEnergyTarget κ C2 C3

theorem finalRouteABClosureTarget_of_consumption_and_residual
    {κ C2 C3 : ℝ}
    (hMain : RouteABConsumptionTarget κ)
    (hErr : RouteVisibleResidualEnergyTarget κ C2 C3) :
    FinalRouteABClosureTarget κ C2 C3 := by
  refine ⟨?_, ?_, hErr⟩
  · exact routeATarget_of_routeABConsumptionTarget hMain
  · exact routeBTarget_of_routeABConsumptionTarget hMain

theorem finalRouteABClosureTarget_of_routeABClosureTarget
    {κ C2 C3 : ℝ}
    (h : RouteABClosureTarget κ C2 C3) :
    FinalRouteABClosureTarget κ C2 C3 :=
  finalRouteABClosureTarget_of_consumption_and_residual h.main_target h.residual_target

theorem finalRouteABClosureTarget_of_endpoint_and_meanApprox
    (e : HalfMassRecenteredEndpoint)
    {C2m C3m : ℝ}
    (hm : MeanChannelApproxTarget C2m C3m) :
    FinalRouteABClosureTarget e.κ
      (2 * (e.C2 + C2m)) (2 * (e.C3 + C3m)) :=
  finalRouteABClosureTarget_of_routeABClosureTarget <|
    FinalRouteClosureTarget.to_routeABClosureTarget
      (finalRouteClosureTarget_of_endpoint_and_meanApprox e hm)

end

end Goldbach.Cert.MajorArcModules.Q0MinorRouteABTargets
