import Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
import Goldbach.Cert.MajorArcModules.Q0MinorRouteABContract

/-!
Thin downstream Route A / Route B placeholder targets.

This file is the first consumer of the public `Q0MinorRouteABContract`.  It does not use the
bridge implementation details directly.  Its job is only to expose the theorem-shaped objects that
future Route A / Route B arguments should consume.

At the current stage these targets are intentionally thin: they restate the structured handled
model split and the exact canonical minor-residual decomposition exported by the contract, and pair
them with the residual-energy target.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorRouteABDownstream

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorRouteABContract
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- Placeholder Route A target consumed only from the public route contract. -/
structure RouteADownstreamTarget (κ : ℝ) : Prop where
  handled_split :
    ∀ X N,
      routeHandledModelAtScalar κ X N
        =
      routeHandledGeometricPart X N + routeHandledZeroModeShapePart κ X N

/-- Placeholder Route B target consumed only from the public route contract. -/
structure RouteBDownstreamTarget (κ : ℝ) : Prop where
  residual_split :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        minorResidual X N Δ_canon
          =
        routeHandledGeometricPart X N
          + routeHandledZeroModeShapePart κ X N
          + routeVisibleResidualOfHalfMassScalar κ X N

theorem routeADownstreamTarget_of_contract
    {κ : ℝ} (h : RouteAConsumptionTarget κ) :
    RouteADownstreamTarget κ :=
  ⟨h.handled_split⟩

theorem routeBDownstreamTarget_of_contract
    {κ : ℝ} (h : RouteBConsumptionTarget κ) :
    RouteBDownstreamTarget κ :=
  ⟨h.residual_split⟩

/-- Downstream Route A / Route B packet paired with the residual-energy target. -/
structure FinalRouteABDownstreamTarget (κ C2 C3 : ℝ) : Prop where
  routeA_target : RouteADownstreamTarget κ
  routeB_target : RouteBDownstreamTarget κ
  residual_target : RouteVisibleResidualEnergyTarget κ C2 C3

theorem finalRouteABDownstreamTarget_of_contract
    {κ C2 C3 : ℝ}
    (h : Q0MinorRouteABContractTarget κ C2 C3) :
    FinalRouteABDownstreamTarget κ C2 C3 := by
  refine ⟨?_, ?_, h.residual_target⟩
  · exact routeADownstreamTarget_of_contract h.routeA_target
  · exact routeBDownstreamTarget_of_contract h.routeB_target

theorem finalRouteABDownstreamTarget_of_endpoint_and_meanApprox
    (e : HalfMassRecenteredEndpoint)
    {C2m C3m : ℝ}
    (hm : MeanChannelApproxTarget C2m C3m) :
    FinalRouteABDownstreamTarget e.κ
      (2 * (e.C2 + C2m)) (2 * (e.C3 + C3m)) :=
  finalRouteABDownstreamTarget_of_contract <|
    q0MinorRouteABContractTarget_of_endpoint_and_meanApprox e hm

end

end Goldbach.Cert.MajorArcModules.Q0MinorRouteABDownstream
