import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets

/-!
# Joint q=1 / q≥2 freeze-energy experiment

This file is intentionally a small theorem surface for the next arithmetic experiment.

The q=1-only β-energy route is frozen as negative evidence.  The new object below keeps the
corrected principal-arc defect and the weighted q≥2 freeze defect together before taking β-norms,
so that any cancellation at the singular β-loci is still available to the proof.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeJointEnergyTargets

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowRankMainTerm
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- Raw β-integrand endpoint for the corrected q=1 freeze defect. -/
noncomputable def canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint
    (X N : ℕ) (β : ℝ) : ℂ :=
  ((((X : ℝ) : ℂ))⁻¹)
    * (∫ u in (0 : ℝ)..(1 : ℝ), q1PhaseCorrectedDoubleSumShellDefect X N u β)

/--
Raw β-integrand endpoint for the already weighted `q ≥ 2` freeze defect.

This is deliberately kept before β-integration.  It is definitionally the `β`-slice corresponding
to the summed `AqCRescaled - AqFrozenC` block in the exact freeze identity.
-/
noncomputable def canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint
    (X N : ℕ) (β : ℝ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
    * (∑ q ∈ Finset.Icc (2 : ℕ) Q0,
        ((((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
              * (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
              * (∫ u : ℝ,
                  (centeredUnitSet (1 : ℝ)).indicator
                    (fun u => smallBetaRescaledArchShell X N q u β) u))
            -
            (((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
              * (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
              * (∫ u : ℝ,
                  (centeredUnitSet (1 : ℝ)).indicator
                    (fun u => smallBetaFrozenRescaledArchShell N u β) u)))
          * qPhaseFactor q N)

/-- Raw β-integrand endpoint for the joint corrected freeze discrepancy. -/
noncomputable def canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint
    (X N : ℕ) (β : ℝ) : ℂ :=
  canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint X N β
    + canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint X N β

/--
Joint pre-absolute ordered-pair β-integrand.

This is the new live object: q=1 and weighted `q ≥ 2` are combined before taking norms.
-/
noncomputable def canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand
    (X N M : ℕ) (β : ℝ) : ℂ :=
  betaSmallSet.indicator
    (fun β : ℝ =>
      canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint X N β
        - canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint X M β) β

/-- The ordered-pair q=1 part of the joint β-preabsolute integrand. -/
noncomputable def canonicalCorrectedFreezeDiscrepancyQ1BetaPairEndpoint
    (X N M : ℕ) (β : ℝ) : ℂ :=
  canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint X N β
    - canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint X M β

/-- The ordered-pair weighted `q ≥ 2` part of the joint β-preabsolute integrand. -/
noncomputable def canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaPairEndpoint
    (X N M : ℕ) (β : ℝ) : ℂ :=
  canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint X N β
    - canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint X M β

/--
Pure algebraic split of the joint β-preabsolute integrand into the q=1 corrected endpoint and
the weighted `q ≥ 2` endpoint.

This is the local rewrite that must be used before any norm is taken.
-/
theorem canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand_eq_q1_add_weightedGe2
    (X N M : ℕ) (β : ℝ) :
    canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand X N M β
      =
    betaSmallSet.indicator
      (fun β : ℝ =>
        canonicalCorrectedFreezeDiscrepancyQ1BetaPairEndpoint X N M β
          + canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaPairEndpoint X N M β) β := by
  unfold canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand
    canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint
    canonicalCorrectedFreezeDiscrepancyQ1BetaPairEndpoint
    canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaPairEndpoint
  by_cases hβ : β ∈ betaSmallSet
  · simp [Set.indicator_of_mem hβ]
    ring
  · simp [Set.indicator_of_notMem hβ]

/-- q=1 endpoint integrates to the existing corrected q=1 freeze-defect block. -/
theorem integral_canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint_eq
    (X N : ℕ) :
    (∫ β in aβ..bβ,
        betaSmallSet.indicator
          (fun β : ℝ => canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint X N β) β)
      =
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalCorrectedFreezeIntegralDoubleSumDefect X N := by
  unfold canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalCorrectedFreezeIntegralDoubleSumDefect
  simp_rw [Set.indicator_const_mul]
  rw [intervalIntegral.integral_const_mul]

/-!
### Singular-part decomposition surface

The next experiment should not try to prove the strongest regularized/divisibility form first.
Instead, isolate the plus/minus pole principal parts of the q=1 endpoint and of the weighted
`q ≥ 2` endpoint, prove exact cancellation of those principal parts, and only then estimate the
regular remainders.
-/

/--
Data for a singular-part decomposition of the joint raw β endpoint.

The next real proof is to instantiate this structure with the actual plus/minus pole terms,
not with a vacuous choice of principal parts.
-/
structure CanonicalCorrectedFreezeDiscrepancySingularPartData where
  q1Plus : ℕ → ℕ → ℝ → ℂ
  q1Minus : ℕ → ℕ → ℝ → ℂ
  q1Regular : ℕ → ℕ → ℝ → ℂ
  weightedGe2Plus : ℕ → ℕ → ℝ → ℂ
  weightedGe2Minus : ℕ → ℕ → ℝ → ℂ
  weightedGe2Regular : ℕ → ℕ → ℝ → ℂ
  q1_decomp :
    ∀ X N β,
      canonicalCorrectedFreezeDiscrepancyQ1BetaRawEndpoint X N β
        =
      (q1Plus X N β + q1Minus X N β) + q1Regular X N β
  weightedGe2_decomp :
    ∀ X N β,
      canonicalCorrectedFreezeDiscrepancyWeightedGe2BetaRawEndpoint X N β
        =
      (weightedGe2Plus X N β + weightedGe2Minus X N β) + weightedGe2Regular X N β
  plus_cancel :
    ∀ X N β,
      q1Plus X N β + weightedGe2Plus X N β = 0
  minus_cancel :
    ∀ X N β,
      q1Minus X N β + weightedGe2Minus X N β = 0

/-- Joint raw endpoint after singular principal-part cancellation. -/
noncomputable def canonicalCorrectedFreezeDiscrepancyRegularRemainderEndpoint
    (D : CanonicalCorrectedFreezeDiscrepancySingularPartData)
    (X N : ℕ) (β : ℝ) : ℂ :=
  D.q1Regular X N β + D.weightedGe2Regular X N β

theorem canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint_eq_regularRemainder
    (D : CanonicalCorrectedFreezeDiscrepancySingularPartData)
    (X N : ℕ) (β : ℝ) :
    canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint X N β
      =
    canonicalCorrectedFreezeDiscrepancyRegularRemainderEndpoint D X N β := by
  rw [canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint, D.q1_decomp, D.weightedGe2_decomp,
    canonicalCorrectedFreezeDiscrepancyRegularRemainderEndpoint]
  have hplus := D.plus_cancel X N β
  have hminus := D.minus_cancel X N β
  ring_nf at hplus hminus ⊢
  simp [hplus, hminus]

/-- β-energy of the joint ordered-pair freeze discrepancy. -/
noncomputable def canonicalCorrectedFreezeDiscrepancyBetaEnergy
    (X N M : ℕ) : ℝ :=
  ∫ β in aβ..bβ,
    ‖canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand X N M β‖ ^ 2

/-- Ordered-pair β-energy of the joint freeze discrepancy on the even window. -/
noncomputable def canonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then canonicalCorrectedFreezeDiscrepancyBetaEnergy X N M else 0

/-- Ordered-pair post-β-integral energy for the joint freeze discrepancy. -/
noncomputable def canonicalCorrectedFreezeDiscrepancyOrderedPairwiseWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then
        ‖∫ β in aβ..bβ,
            canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand X N M β‖ ^ 2
      else 0

/--
Exact endpoint representation of the trusted corrected freeze discrepancy.

This is a theorem surface for connecting the new β-preabsolute endpoint to the existing exact
freeze identity.
-/
structure CanonicalCorrectedFreezeDiscrepancyBetaEndpointRepresentation : Prop where
  endpoint_eq :
    ∀ {X N : ℕ}, 2 ≤ X →
      canonicalCorrectedFreezeDiscrepancy X N
        =
      ∫ β in aβ..bβ,
        betaSmallSet.indicator
          (fun β : ℝ => canonicalCorrectedFreezeDiscrepancyBetaRawEndpoint X N β) β

/--
The local pole-cancellation theorem surface.

The intended proof is an exact algebraic regularization of the combined q=1/q≥2 β-integrand:
the first-order singular pieces at `β = ± u / X` must cancel before any β-norm is taken.
-/
structure CanonicalCorrectedFreezeDiscrepancyBetaPoleCancellation where
  A : ℕ → ℕ → ℕ → ℝ → ℝ → ℂ
  B : ℕ → ℕ → ℕ → ℝ → ℝ → ℂ
  eq_regularized :
    ∀ X N M β,
      canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand X N M β
        =
      betaSmallSet.indicator
        (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ),
            (((β - u / (X : ℝ) : ℝ) : ℂ) * A X N M u β
              + (((β + u / (X : ℝ) : ℝ) : ℂ) * B X N M u β))) β

/--
Route-sized β-energy target for the joint discrepancy.

Since `card (EvenIn X H) ~ H`, this is the theorem-facing `H / Q0^2` scale.
-/
structure CanonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergyTarget
    (Cjoint : ℝ) : Prop where
  Cjoint_nonneg : 0 ≤ Cjoint
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalCorrectedFreezeDiscrepancyOrderedPairwiseBetaEnergy X
        ≤
      Cjoint * (((EvenIn X H).card : ℝ) / ((Q0 : ℝ) ^ 2))

/--
β-L² transport surface for the joint discrepancy.

The q=1-only version has already shown the right formal shape; the joint branch should reuse that
method after the pole-cancellation and β-energy target are available.
-/
structure CanonicalCorrectedFreezeDiscrepancyBetaL2Transport : Prop where
  bound :
    ∀ X N M,
      ‖∫ β in aβ..bβ,
          canonicalCorrectedFreezeDiscrepancyBetaPreAbsoluteIntegrand X N M β‖ ^ 2
        ≤
      ((1 : ℝ) / 6) * canonicalCorrectedFreezeDiscrepancyBetaEnergy X N M

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeJointEnergyTargets
