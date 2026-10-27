import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveClosure
import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanNoncoprime

/-!
# Analytic input surface for the signed-conductor Type-I reduction

The preceding modules reduce the active coprime Type-I progression error exactly to three terms:

* the centered principal `psi` sum;
* primitive-character families at conductors `r > 1`; and
* an explicit induced-character correction.

This file packages only maximal bounds for the ordinary cumulative `psi` sums.  The weighted
Type-I conclusion is derived from those bounds by the finite Stieltjes theorem and the signed
conductor-variation estimate.  Consequently this interface does not assume the cancellation it
is intended to prove.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveAnalyticInterface

open scoped BigOperators
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanNoncoprime
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveMeanValue
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveReindexing
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveClosure
open Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrectionSharp

noncomputable section

/--
The narrow analytic input left by the exact reduction.  Its fields bound ordinary cumulative
Dirichlet-character sums on the exact interval used by the balanced Type-I term.
-/
structure PrimitivePsiMaxInput (L N u : ℕ) where
  principalMax : ℝ
  primitiveMax : (r : ℕ) → DirichletCharacter ℂ r → ℝ
  principalMax_nonneg : 0 ≤ principalMax
  principal_bound :
    ∀ t ∈ Finset.Icc (L - 1) (N - L), ‖principalPsiError t‖ ≤ principalMax
  primitiveMax_nonneg :
    ∀ r ∈ nonprincipalPrimitiveConductorSupport N u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ primitiveMax r χ
  primitive_bound :
    ∀ r ∈ nonprincipalPrimitiveConductorSupport N u,
      ∀ χ ∈ primitiveCharacters r,
        ∀ t ∈ Finset.Icc (L - 1) (N - L),
          ‖dirichletPsi t r χ‖ ≤ primitiveMax r χ

/-- Endpoint-and-variation cost for a primitive conductor. -/
noncomputable def primitiveConductorAnalyticCost (N r : ℕ) : ℝ :=
  2 * (6 * ((r * N : ℕ) : ℝ) / (Nat.totient (r * N) : ℝ) /
    (Nat.totient r : ℝ)) * Real.log (N : ℝ)

/-- Allowance for the centered conductor-one family. -/
noncomputable def principalConductorAnalyticAllowance
    (N : ℕ) (M : ℝ) : ℝ :=
  M * (2 * (6 * (N : ℝ) / (Nat.totient N : ℝ)) * Real.log (N : ℝ))

/-- Sum of the maximal primitive-character masses with their signed-conductor costs. -/
noncomputable def nonprincipalConductorAnalyticAllowance
    (N u : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
    (∑ χ ∈ primitiveCharacters r, M r χ) * primitiveConductorAnalyticCost N r

/-- The conventional primitive-character mean-value mass up to conductor `u`. -/
noncomputable def primitiveCharacterMeanValueMass
    (u : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 u,
    ((r : ℝ) / (Nat.totient r : ℝ)) *
      ∑ χ ∈ primitiveCharacters r, M r χ

/-- Global factor converting a standard primitive mean-value mass into the project allowance. -/
noncomputable def primitiveMeanValueGlobalFactor (N : ℕ) : ℝ :=
  12 * (N : ℝ) / (Nat.totient N : ℝ) * Real.log (N : ℝ)

/-- Elementary allowance already proved for all induced-character corrections. -/
noncomputable def inducedCharacterAnalyticAllowance (N u : ℕ) : ℝ :=
  (u : ℝ) *
    (Real.log (N : ℝ) *
      ((Real.log (u : ℝ) / Real.log 2) * Real.log (N : ℝ)))

/-- The complete analytic allowance supplied by a `PrimitivePsiMaxInput`. -/
noncomputable def activeCoprimeAnalyticAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u) : ℝ :=
  principalConductorAnalyticAllowance N input.principalMax +
    nonprincipalConductorAnalyticAllowance N u input.primitiveMax +
      inducedCharacterAnalyticAllowance N u

/-- Exact small-conductor part of the nonprincipal allowance. -/
noncomputable def nonprincipalConductorAnalyticAllowanceUpTo
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => r ≤ R),
    (∑ χ ∈ primitiveCharacters r, M r χ) * primitiveConductorAnalyticCost N r

/-- Exact large-conductor part of the nonprincipal allowance. -/
noncomputable def nonprincipalConductorAnalyticAllowanceAbove
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ r ∈ (nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r),
    (∑ χ ∈ primitiveCharacters r, M r χ) * primitiveConductorAnalyticCost N r

/-- The exact nonprincipal allowance splits at every conductor cutoff. -/
theorem nonprincipalConductorAnalyticAllowance_eq_upTo_add_above
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) :
    nonprincipalConductorAnalyticAllowance N u M =
      nonprincipalConductorAnalyticAllowanceUpTo N u R M +
        nonprincipalConductorAnalyticAllowanceAbove N u R M := by
  classical
  unfold nonprincipalConductorAnalyticAllowance
    nonprincipalConductorAnalyticAllowanceUpTo
    nonprincipalConductorAnalyticAllowanceAbove
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := nonprincipalPrimitiveConductorSupport N u)
      (p := fun r => r ≤ R)
      (f := fun r =>
        (∑ χ ∈ primitiveCharacters r, M r χ) *
          primitiveConductorAnalyticCost N r)).symm

/-- Coprime allowance after independent small- and large-conductor estimates. -/
noncomputable def activeCoprimeSplitAnalyticAllowance
    (N u : ℕ) (principalMax smallBound largeBound : ℝ) : ℝ :=
  principalConductorAnalyticAllowance N principalMax + smallBound + largeBound +
    inducedCharacterAnalyticAllowance N u

/-- Closed allowance after a standard primitive mean-value mass is bounded by `B`. -/
noncomputable def activeCoprimeMeanValueAllowance
    (N u : ℕ) (principalMax B : ℝ) : ℝ :=
  principalConductorAnalyticAllowance N principalMax +
    primitiveMeanValueGlobalFactor N * B +
      inducedCharacterAnalyticAllowance N u

/-- Complete short Type-I allowance after adding the elementary noncoprime branch. -/
noncomputable def activeTypeIMeanValueAllowance
    (N u : ℕ) (principalMax B : ℝ) : ℝ :=
  activeCoprimeMeanValueAllowance N u principalMax B +
    balancedVaughanTypeINoncoprimeExplicitBound N u

/-- Complete short Type-I allowance with distinct conductor-range bounds. -/
noncomputable def activeTypeISplitAnalyticAllowance
    (N u : ℕ) (principalMax smallBound largeBound : ℝ) : ℝ :=
  activeCoprimeSplitAnalyticAllowance N u principalMax smallBound largeBound +
    balancedVaughanTypeINoncoprimeExplicitBound N u

/--
For a conductor coprime to the center, the project-specific endpoint cost is bounded by the
standard primitive mean-value weight times one center-dependent global factor.
-/
theorem primitiveConductorAnalyticCost_le_meanValueWeight
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (hNr : Nat.Coprime N r) :
    primitiveConductorAnalyticCost N r ≤
      primitiveMeanValueGlobalFactor N *
        ((r : ℝ) / (Nat.totient r : ℝ)) := by
  have hTotientN : (0 : ℝ) < Nat.totient N := by
    exact_mod_cast Nat.totient_pos.2 hN
  have hTotientR : (0 : ℝ) < Nat.totient r := by
    exact_mod_cast Nat.totient_pos.2 hr
  have hTotientROne : (1 : ℝ) ≤ Nat.totient r := by
    exact_mod_cast Nat.totient_pos.2 hr
  have hLogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hFactorNonneg :
      0 ≤ primitiveMeanValueGlobalFactor N *
        ((r : ℝ) / (Nat.totient r : ℝ)) := by
    unfold primitiveMeanValueGlobalFactor
    positivity
  have hInvLe : (1 : ℝ) / (Nat.totient r : ℝ) ≤ 1 :=
    (div_le_one₀ hTotientR).2 hTotientROne
  have hEq :
      primitiveConductorAnalyticCost N r =
        (primitiveMeanValueGlobalFactor N *
          ((r : ℝ) / (Nat.totient r : ℝ))) *
            (1 / (Nat.totient r : ℝ)) := by
    unfold primitiveConductorAnalyticCost primitiveMeanValueGlobalFactor
    rw [Nat.totient_mul hNr.symm]
    push_cast
    field_simp
    ring
  rw [hEq]
  exact mul_le_of_le_one_right hFactorNonneg hInvLe

/-- The nonprincipal project support lies in the conventional range `2 ≤ r ≤ u`. -/
theorem nonprincipalPrimitiveConductorSupport_subset_Icc
    (N u : ℕ) :
    nonprincipalPrimitiveConductorSupport N u ⊆ Finset.Icc 2 u := by
  intro r hr
  have hrData := mem_nonprincipalPrimitiveConductorSupport_iff.mp hr
  have hrSupport := Finset.mem_filter.mp hrData.1
  have hrBounds := Finset.mem_Icc.mp hrSupport.1
  rw [Finset.mem_Icc]
  exact ⟨by omega, hrBounds.2⟩

/--
The full nonprincipal allowance is controlled by the conventional aggregate primitive-character
mass.  This is the finite compatibility theorem needed to apply a published mean-value estimate.
-/
theorem nonprincipalConductorAnalyticAllowance_le_meanValueMass
    {N u : ℕ} (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ)
    (hN : 0 < N)
    (hM : ∀ r ∈ Finset.Icc 2 u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ M r χ) :
    nonprincipalConductorAnalyticAllowance N u M ≤
      primitiveMeanValueGlobalFactor N * primitiveCharacterMeanValueMass u M := by
  have hFactor : 0 ≤ primitiveMeanValueGlobalFactor N := by
    unfold primitiveMeanValueGlobalFactor
    have hTotientN : (0 : ℝ) < Nat.totient N := by
      exact_mod_cast Nat.totient_pos.2 hN
    have hLogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    positivity
  have hSubset := nonprincipalPrimitiveConductorSupport_subset_Icc N u
  have hTerm : ∀ r ∈ nonprincipalPrimitiveConductorSupport N u,
      (∑ χ ∈ primitiveCharacters r, M r χ) * primitiveConductorAnalyticCost N r ≤
        primitiveMeanValueGlobalFactor N *
          (((r : ℝ) / (Nat.totient r : ℝ)) *
            ∑ χ ∈ primitiveCharacters r, M r χ) := by
    intro r hr
    have hrRange : r ∈ Finset.Icc 2 u := hSubset hr
    have hrData := (mem_nonprincipalPrimitiveConductorSupport_iff.mp hr).1
    have hrSupport := Finset.mem_filter.mp hrData
    have hrBounds := Finset.mem_Icc.mp hrSupport.1
    have hrPos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hrBounds.1
    have hMassNonneg : 0 ≤ ∑ χ ∈ primitiveCharacters r, M r χ := by
      apply Finset.sum_nonneg
      intro χ hχ
      exact hM r hrRange χ hχ
    calc
      (∑ χ ∈ primitiveCharacters r, M r χ) *
          primitiveConductorAnalyticCost N r ≤
          (∑ χ ∈ primitiveCharacters r, M r χ) *
            (primitiveMeanValueGlobalFactor N *
              ((r : ℝ) / (Nat.totient r : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (primitiveConductorAnalyticCost_le_meanValueWeight hN hrPos hrSupport.2)
          hMassNonneg
      _ = primitiveMeanValueGlobalFactor N *
          (((r : ℝ) / (Nat.totient r : ℝ)) *
            ∑ χ ∈ primitiveCharacters r, M r χ) := by ring
  unfold nonprincipalConductorAnalyticAllowance primitiveCharacterMeanValueMass
  calc
    (∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
        (∑ χ ∈ primitiveCharacters r, M r χ) *
          primitiveConductorAnalyticCost N r) ≤
        ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
          primitiveMeanValueGlobalFactor N *
            (((r : ℝ) / (Nat.totient r : ℝ)) *
              ∑ χ ∈ primitiveCharacters r, M r χ) :=
      Finset.sum_le_sum hTerm
    _ = primitiveMeanValueGlobalFactor N *
        ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
          (((r : ℝ) / (Nat.totient r : ℝ)) *
            ∑ χ ∈ primitiveCharacters r, M r χ) := by
      rw [Finset.mul_sum]
    _ ≤ primitiveMeanValueGlobalFactor N *
        ∑ r ∈ Finset.Icc 2 u,
          (((r : ℝ) / (Nat.totient r : ℝ)) *
            ∑ χ ∈ primitiveCharacters r, M r χ) := by
      apply mul_le_mul_of_nonneg_left _ hFactor
      apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
      intro r hrRange hrNotSupport
      have hrBounds := Finset.mem_Icc.mp hrRange
      have hrPos : 0 < r := by omega
      have hTotientR : (0 : ℝ) < Nat.totient r := by
        exact_mod_cast Nat.totient_pos.2 hrPos
      have hMassNonneg : 0 ≤ ∑ χ ∈ primitiveCharacters r, M r χ := by
        apply Finset.sum_nonneg
        intro χ hχ
        exact hM r hrRange χ hχ
      positivity

/-- The principal field of the input controls the centered conductor-one contribution. -/
theorem norm_principalCenteredConductorSum_le_input
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N) :
    ‖principalCenteredConductorSum N u L (N - L)‖ ≤
      principalConductorAnalyticAllowance N input.principalMax := by
  have hN : 0 < N := by omega
  have hInterval : L ≤ N - L := by omega
  have hRight : N - L < N := by omega
  simpa [principalConductorAnalyticAllowance] using
    (norm_principalCenteredConductorSum_le input.principalMax hN hL hInterval hRight
      input.principalMax_nonneg input.principal_bound)

/-- The primitive fields of the input control all nonprincipal conductor families. -/
theorem norm_nonprincipalConductorFamilies_le_input
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N) :
    ‖∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
        primitiveCharacterFamilyConductorSum N u r L (N - L)‖ ≤
      nonprincipalConductorAnalyticAllowance N u input.primitiveMax := by
  have hN : 0 < N := by omega
  have hInterval : L ≤ N - L := by omega
  have hRight : N - L < N := by omega
  unfold nonprincipalConductorAnalyticAllowance
  calc
    ‖∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
        primitiveCharacterFamilyConductorSum N u r L (N - L)‖ ≤
        ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
          ‖primitiveCharacterFamilyConductorSum N u r L (N - L)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
        (∑ χ ∈ primitiveCharacters r, input.primitiveMax r χ) *
          primitiveConductorAnalyticCost N r := by
      apply Finset.sum_le_sum
      intro r hr
      have hrSupport := (mem_nonprincipalPrimitiveConductorSupport_iff.mp hr).1
      have hrData := Finset.mem_filter.mp hrSupport
      have hrBounds := Finset.mem_Icc.mp hrData.1
      have hrPos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hrBounds.1
      simpa [primitiveConductorAnalyticCost] using
        (norm_primitiveCharacterFamilyConductorSum_le
          (input.primitiveMax r) hN hrPos hrData.2 hL hInterval hRight
          (input.primitiveMax_nonneg r hr) (input.primitive_bound r hr))

/-- The sharp elementary correction theorem exactly supplies the correction allowance. -/
theorem norm_activeInducedCorrection_le_allowance
    {L N u : ℕ} (hN : 0 < N) (hu : 0 < u) :
    ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
      inducedCharacterAnalyticAllowance N u := by
  simpa [inducedCharacterAnalyticAllowance] using
    (norm_activePrimitiveCharacterTotalInducedCorrection_le
      (L := L) (N := N) (u := u) hN hu)

/--
Quantitative endpoint of the signed-conductor reduction.  Any explicit character theorem can be
used by constructing `PrimitivePsiMaxInput`; the weighted Type-I error bound then follows without
an unrestricted maximal Bombieri--Vinogradov hypothesis.
-/
theorem norm_activeCoprimeProgressionError_le_analyticAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hStable : PrimitiveCharacterChangeLevelStable) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeAnalyticAllowance input := by
  have hN : 0 < N := by omega
  rw [activeCoprimeProgressionError_cast_eq_principal_add_nonprincipal_sub_induced
    hL hu hStable]
  calc
    ‖principalCenteredConductorSum N u L (N - L) +
        (∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
          primitiveCharacterFamilyConductorSum N u r L (N - L)) -
        activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
        ‖principalCenteredConductorSum N u L (N - L) +
          (∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
            primitiveCharacterFamilyConductorSum N u r L (N - L))‖ +
          ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ :=
      norm_sub_le _ _
    _ ≤ (‖principalCenteredConductorSum N u L (N - L)‖ +
          ‖∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
            primitiveCharacterFamilyConductorSum N u r L (N - L)‖) +
          ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ := by
      exact add_le_add_right (norm_add_le _ _) _
    _ ≤ principalConductorAnalyticAllowance N input.principalMax +
          nonprincipalConductorAnalyticAllowance N u input.primitiveMax +
          inducedCharacterAnalyticAllowance N u := by
      exact add_le_add
        (add_le_add
          (norm_principalCenteredConductorSum_le_input input hL hTwoL)
          (norm_nonprincipalConductorFamilies_le_input input hL hTwoL))
        (norm_activeInducedCorrection_le_allowance hN hu)
    _ = activeCoprimeAnalyticAllowance input := rfl

/--
Exact cutoff-facing endpoint. Independent estimates for conductors at most `R` and above `R`
combine without replacing either range by the coarser all-conductor mass.
-/
theorem norm_activeCoprimeProgressionError_le_splitAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (smallBound largeBound : ℝ)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hSmall :
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax ≤ smallBound)
    (hLarge :
      nonprincipalConductorAnalyticAllowanceAbove N u R input.primitiveMax ≤ largeBound) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeSplitAnalyticAllowance
        N u input.principalMax smallBound largeBound := by
  calc
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
        activeCoprimeAnalyticAllowance input :=
      norm_activeCoprimeProgressionError_le_analyticAllowance
        input hL hu hTwoL hStable
    _ = principalConductorAnalyticAllowance N input.principalMax +
          (nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax +
            nonprincipalConductorAnalyticAllowanceAbove N u R input.primitiveMax) +
          inducedCharacterAnalyticAllowance N u := by
      rw [activeCoprimeAnalyticAllowance,
        nonprincipalConductorAnalyticAllowance_eq_upTo_add_above]
    _ ≤ principalConductorAnalyticAllowance N input.principalMax +
          (smallBound + largeBound) + inducedCharacterAnalyticAllowance N u := by
      exact add_le_add_right
        (add_le_add_left (add_le_add hSmall hLarge)
          (principalConductorAnalyticAllowance N input.principalMax)) _
    _ = activeCoprimeSplitAnalyticAllowance
          N u input.principalMax smallBound largeBound := by
      unfold activeCoprimeSplitAnalyticAllowance
      ring

/-- Add the proved noncoprime branch to the exact conductor-range split. -/
theorem abs_primeResidueSum_sub_activeMain_le_splitAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (smallBound largeBound : ℝ)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hSmall :
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax ≤ smallBound)
    (hLarge :
      nonprincipalConductorAnalyticAllowanceAbove N u R input.primitiveMax ≤ largeBound) :
    |balancedVaughanTypeIPrimeResidueSum L N u -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance
        N u input.principalMax smallBound largeBound := by
  have hLN : L ≤ N := by omega
  have hCoprime :
      |balancedVaughanTypeIActiveCoprimeProgressionError L N u| ≤
        activeCoprimeSplitAnalyticAllowance
          N u input.principalMax smallBound largeBound := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      (norm_activeCoprimeProgressionError_le_splitAllowance
        input smallBound largeBound hL hu hTwoL hStable hSmall hLarge)
  have hNoncoprime :
      |balancedVaughanTypeINoncoprimeProgressionContribution L N u| ≤
        balancedVaughanTypeINoncoprimeExplicitBound N u :=
    abs_balancedVaughanTypeINoncoprimeProgressionContribution_le
      (by omega : 1 ≤ L) hLN
  rw [primeResidueSum_eq_activeMain_add_coprimeError_add_noncoprime]
  calc
    |balancedVaughanTypeIActiveDiscreteCoprimeMain L N u +
          balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u -
          balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| =
        |balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u| := by
      congr 1
      ring
    _ ≤ |balancedVaughanTypeIActiveCoprimeProgressionError L N u| +
          |balancedVaughanTypeINoncoprimeProgressionContribution L N u| :=
      abs_add_le _ _
    _ ≤ activeCoprimeSplitAnalyticAllowance
          N u input.principalMax smallBound largeBound +
          balancedVaughanTypeINoncoprimeExplicitBound N u :=
      add_le_add hCoprime hNoncoprime
    _ = activeTypeISplitAnalyticAllowance
          N u input.principalMax smallBound largeBound := rfl

/--
Complete short Type-I theorem with separate small- and large-conductor analytic inputs.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_splitAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (smallBound largeBound : ℝ)
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hSmall :
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax ≤ smallBound)
    (hLarge :
      nonprincipalConductorAnalyticAllowanceAbove N u R input.primitiveMax ≤ largeBound) :
    |RouteAFiniteWeightBilinearCircle.finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance
        N u input.principalMax smallBound largeBound := by
  rw [balancedVaughanTypeIPrimeConvolution_eq_residueSum hL]
  exact abs_primeResidueSum_sub_activeMain_le_splitAllowance
    input smallBound largeBound (by omega) hu hTwoL hStable hSmall hLarge

/--
Published-theorem-facing endpoint.  Once the conventional primitive-character mass is at most
`B`, the active coprime Type-I error has the displayed closed allowance. This deliberately coarse
corollary is not a replacement for the cutoff theorem above when a large-conductor estimate needs
to retain an additional conductor weight.
-/
theorem norm_activeCoprimeProgressionError_le_meanValueAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u) (B : ℝ)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hM : ∀ r ∈ Finset.Icc 2 u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ input.primitiveMax r χ)
    (hMass : primitiveCharacterMeanValueMass u input.primitiveMax ≤ B) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeMeanValueAllowance N u input.principalMax B := by
  have hN : 0 < N := by omega
  have hFactor : 0 ≤ primitiveMeanValueGlobalFactor N := by
    unfold primitiveMeanValueGlobalFactor
    have hTotientN : (0 : ℝ) < Nat.totient N := by
      exact_mod_cast Nat.totient_pos.2 hN
    have hLogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    positivity
  have hNonprincipal :
      nonprincipalConductorAnalyticAllowance N u input.primitiveMax ≤
        primitiveMeanValueGlobalFactor N *
          primitiveCharacterMeanValueMass u input.primitiveMax :=
    nonprincipalConductorAnalyticAllowance_le_meanValueMass
      input.primitiveMax hN hM
  calc
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
        activeCoprimeAnalyticAllowance input :=
      norm_activeCoprimeProgressionError_le_analyticAllowance
        input hL hu hTwoL hStable
    _ ≤ principalConductorAnalyticAllowance N input.principalMax +
          primitiveMeanValueGlobalFactor N *
            primitiveCharacterMeanValueMass u input.primitiveMax +
          inducedCharacterAnalyticAllowance N u := by
      unfold activeCoprimeAnalyticAllowance
      exact add_le_add_right
        (add_le_add_left hNonprincipal
          (principalConductorAnalyticAllowance N input.principalMax)) _
    _ ≤ principalConductorAnalyticAllowance N input.principalMax +
          primitiveMeanValueGlobalFactor N * B +
          inducedCharacterAnalyticAllowance N u := by
      apply add_le_add_right
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_left hMass hFactor
    _ = activeCoprimeMeanValueAllowance N u input.principalMax B := rfl

/--
The complete prime-in-progressions expression differs from the corrected active discrete main by
the coprime mean-value allowance plus the proved noncoprime prime-power allowance.
-/
theorem abs_primeResidueSum_sub_activeMain_le_meanValueAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u) (B : ℝ)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hM : ∀ r ∈ Finset.Icc 2 u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ input.primitiveMax r χ)
    (hMass : primitiveCharacterMeanValueMass u input.primitiveMax ≤ B) :
    |balancedVaughanTypeIPrimeResidueSum L N u -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeIMeanValueAllowance N u input.principalMax B := by
  have hLN : L ≤ N := by omega
  have hCoprime :
      |balancedVaughanTypeIActiveCoprimeProgressionError L N u| ≤
        activeCoprimeMeanValueAllowance N u input.principalMax B := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      (norm_activeCoprimeProgressionError_le_meanValueAllowance
        input B hL hu hTwoL hStable hM hMass)
  have hNoncoprime :
      |balancedVaughanTypeINoncoprimeProgressionContribution L N u| ≤
        balancedVaughanTypeINoncoprimeExplicitBound N u :=
    abs_balancedVaughanTypeINoncoprimeProgressionContribution_le
      (by omega : 1 ≤ L) hLN
  rw [primeResidueSum_eq_activeMain_add_coprimeError_add_noncoprime]
  calc
    |balancedVaughanTypeIActiveDiscreteCoprimeMain L N u +
          balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u -
          balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| =
        |balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u| := by
      congr 1
      ring
    _ ≤ |balancedVaughanTypeIActiveCoprimeProgressionError L N u| +
          |balancedVaughanTypeINoncoprimeProgressionContribution L N u| :=
      abs_add_le _ _
    _ ≤ activeCoprimeMeanValueAllowance N u input.principalMax B +
          balancedVaughanTypeINoncoprimeExplicitBound N u :=
      add_le_add hCoprime hNoncoprime
    _ = activeTypeIMeanValueAllowance N u input.principalMax B := rfl

/--
Complete short Type-I correlation theorem.  This is the checked bridge from the balanced Vaughan
convolution to the corrected active main; its only unproved inputs are displayed in the theorem
arguments rather than hidden in a certificate.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_meanValueAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u) (B : ℝ)
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hM : ∀ r ∈ Finset.Icc 2 u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ input.primitiveMax r χ)
    (hMass : primitiveCharacterMeanValueMass u input.primitiveMax ≤ B) :
    |RouteAFiniteWeightBilinearCircle.finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeIMeanValueAllowance N u input.principalMax B := by
  rw [balancedVaughanTypeIPrimeConvolution_eq_residueSum hL]
  exact abs_primeResidueSum_sub_activeMain_le_meanValueAllowance
    input B (by omega) hu hTwoL hStable hM hMass

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveAnalyticInterface
