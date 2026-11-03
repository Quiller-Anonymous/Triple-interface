import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLocalizedHybrid

/-!
# Canonical finite maxima for the balanced Vaughan Type-I interface

The analytic Type-I endpoint is phrased using a `PrimitivePsiMaxInput`.  Such an input should not
itself be an additional existence obligation: all endpoint ranges are finite.  This file defines
canonical maxima using finite suprema in `NNReal`, proves their pointwise bounds, and inserts the
resulting record into the algebraically unconditional localized endpoint.

The two aggregate estimates in the final theorem remain the genuine external analytic inputs.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanCanonicalPsiMax

open scoped BigOperators NNReal
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveClosure
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveAnalyticInterface
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLargeConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLocalizedHybrid
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightBilinearCircle
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberClosure

noncomputable section

/-- Exact finite maximum of the centered principal `psi` sum on the Type-I interval. -/
def principalPsiIntervalMax (L N : ℕ) : ℝ :=
  ((Finset.Icc (L - 1) (N - L)).sup fun t => ‖principalPsiError t‖₊ : ℝ≥0)

/-- Exact finite maximum of one primitive-character `psi` sum on the Type-I interval. -/
def primitivePsiIntervalMax
    (L N r : ℕ) (χ : DirichletCharacter ℂ r) : ℝ :=
  ((Finset.Icc (L - 1) (N - L)).sup fun t => ‖dirichletPsi t r χ‖₊ : ℝ≥0)

theorem principalPsiIntervalMax_nonneg (L N : ℕ) :
    0 ≤ principalPsiIntervalMax L N := by
  unfold principalPsiIntervalMax
  positivity

theorem primitivePsiIntervalMax_nonneg
    (L N r : ℕ) (χ : DirichletCharacter ℂ r) :
    0 ≤ primitivePsiIntervalMax L N r χ := by
  unfold primitivePsiIntervalMax
  positivity

theorem norm_principalPsiError_le_intervalMax
    {L N t : ℕ} (ht : t ∈ Finset.Icc (L - 1) (N - L)) :
    ‖principalPsiError t‖ ≤ principalPsiIntervalMax L N := by
  unfold principalPsiIntervalMax
  exact_mod_cast (Finset.le_sup (f := fun s => ‖principalPsiError s‖₊) ht)

theorem norm_dirichletPsi_le_intervalMax
    {L N r t : ℕ} {χ : DirichletCharacter ℂ r}
    (ht : t ∈ Finset.Icc (L - 1) (N - L)) :
    ‖dirichletPsi t r χ‖ ≤ primitivePsiIntervalMax L N r χ := by
  unfold primitivePsiIntervalMax
  exact_mod_cast (Finset.le_sup (f := fun s => ‖dirichletPsi s r χ‖₊) ht)

/-- Canonical realization of the finite maximal-`psi` input surface. -/
def canonicalPrimitivePsiMaxInput (L N u : ℕ) : PrimitivePsiMaxInput L N u where
  principalMax := principalPsiIntervalMax L N
  primitiveMax := primitivePsiIntervalMax L N
  principalMax_nonneg := principalPsiIntervalMax_nonneg L N
  principal_bound := by
    intro t ht
    exact norm_principalPsiError_le_intervalMax ht
  primitiveMax_nonneg := by
    intro r hr χ hχ
    exact primitivePsiIntervalMax_nonneg L N r χ
  primitive_bound := by
    intro r hr χ hχ t ht
    exact norm_dirichletPsi_le_intervalMax ht

/--
Canonical localized Type-I endpoint.  The maxima are now concrete finite suprema; only their
small-conductor aggregate and large-conductor mean-value estimates remain as hypotheses.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_canonicalLocalizedHybrid
    {L N u R : ℕ} {smallBound massBound : ℝ}
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hSmall : nonprincipalConductorAnalyticAllowanceUpTo N u R
      (primitivePsiIntervalMax L N) ≤ smallBound)
    (hMass : largeConductorPrimitiveMeanValueMass N u R
      (primitivePsiIntervalMax L N) ≤ massBound) :
    |finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance N u (principalPsiIntervalMax L N) smallBound
        (representedLargeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) * massBound) := by
  simpa [canonicalPrimitivePsiMaxInput] using
    (abs_typeIPrimeConvolution_sub_activeMain_le_localizedHybridMeanValueAllowance_unconditional
      (input := canonicalPrimitivePsiMaxInput L N u)
      hL hu hTwoL hR hSmall hMass)

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanCanonicalPsiMax
