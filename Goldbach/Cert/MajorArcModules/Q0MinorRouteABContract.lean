import Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
import Goldbach.Cert.MajorArcModules.Q0MinorRouteABTargets

/-!
Public downstream contract for the route-visible Vaughan bridge.

This file is intentionally thin. It does not expose the zero-mode provenance ladder or the
internal bridge assembly. It only exports the theorem-shaped promises that downstream Route A / B
consumers should use:

* `RouteAConsumptionTarget`: the structured handled model has already been separated into its
  geometric and zero-mode-shape pieces.
* `RouteBConsumptionTarget`: the canonical minor residual is exactly the sum of those handled
  pieces and the post-model residual.
* `Q0MinorRouteABContractTarget`: Route A, Route B, and the residual-energy ledger inputs are all
  available as a single downstream packet.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorRouteABContract

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorRouteABTargets
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- Downstream Route A contract: the handled model is already split into its two structured parts. -/
structure RouteAConsumptionTarget (κ : ℝ) : Prop where
  handled_split :
    ∀ X N,
      routeHandledModelAtScalar κ X N
        =
      routeHandledGeometricPart X N + routeHandledZeroModeShapePart κ X N

/-- Downstream Route B contract: the exact canonical minor residual is split into handled model plus error. -/
structure RouteBConsumptionTarget (κ : ℝ) : Prop where
  residual_split :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        minorResidual X N Δ_canon
          =
        routeHandledGeometricPart X N
          + routeHandledZeroModeShapePart κ X N
          + routeVisibleResidualOfHalfMassScalar κ X N

theorem routeAConsumptionTarget_of_routeATarget
    {κ : ℝ} (h : RouteATarget κ) :
    RouteAConsumptionTarget κ :=
  ⟨h.handled_split⟩

theorem routeBConsumptionTarget_of_routeBTarget
    {κ : ℝ} (h : RouteBTarget κ) :
    RouteBConsumptionTarget κ :=
  ⟨h.minor_decompose⟩

/--
Single downstream packet for Route A / B integration: both structured model contracts and the
residual-energy target are available without importing bridge internals.
-/
structure Q0MinorRouteABContractTarget (κ C2 C3 : ℝ) : Prop where
  routeA_target : RouteAConsumptionTarget κ
  routeB_target : RouteBConsumptionTarget κ
  residual_target : RouteVisibleResidualEnergyTarget κ C2 C3

theorem q0MinorRouteABContractTarget_of_finalRouteABClosureTarget
    {κ C2 C3 : ℝ}
    (h : FinalRouteABClosureTarget κ C2 C3) :
    Q0MinorRouteABContractTarget κ C2 C3 := by
  refine ⟨?_, ?_, h.residual_target⟩
  · exact routeAConsumptionTarget_of_routeATarget h.routeA_target
  · exact routeBConsumptionTarget_of_routeBTarget h.routeB_target

theorem q0MinorRouteABContractTarget_of_endpoint_and_meanApprox
    (e : HalfMassRecenteredEndpoint)
    {C2m C3m : ℝ}
    (hm : MeanChannelApproxTarget C2m C3m) :
    Q0MinorRouteABContractTarget e.κ
      (2 * (e.C2 + C2m)) (2 * (e.C3 + C3m)) :=
  q0MinorRouteABContractTarget_of_finalRouteABClosureTarget <|
    finalRouteABClosureTarget_of_endpoint_and_meanApprox e hm

end

end Goldbach.Cert.MajorArcModules.Q0MinorRouteABContract
