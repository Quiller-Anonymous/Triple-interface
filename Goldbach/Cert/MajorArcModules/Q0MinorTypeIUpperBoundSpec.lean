import Goldbach.Cert.MajorArcModules.Q0MinorTypeIDeterministic

/-!
Generator-facing window-sum upper-bound target for the ε₁ Type-I / zero-mode piece.

The deterministic algebra already isolates the `t = 0` term and bounds it pointwise. This file
packages the remaining exact window sum that a generator must certify in order to obtain
`canonicalExpansion.ZeroModeEnergyBound U`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundSpec

open scoped BigOperators Interval

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIDeterministic
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- Pointwise deterministic Type-I upper bound from the `t = 0` slice. -/
noncomputable def pointwiseUpper (X N : ℕ) : ℝ :=
  ‖q0NormFactor N‖ ^ 2 *
    (‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2 * diagMass X N)

/-- Exact Type-I window expression that the generator is expected to upper-bound. -/
noncomputable def windowUpper (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, pointwiseUpper X N

lemma typeIPart_sq_le_pointwiseUpper (X : ℕ) {N : ℕ} :
    ‖canonicalExpansion.typeIPart X N‖ ^ 2 ≤ pointwiseUpper X N := by
  simpa [pointwiseUpper] using
    typeIPart_norm_sq_le_complement_weight_sq_mul_diagMass (X := X) (N := N)

theorem sum_typeIPart_sq_le_windowUpper (X : ℕ) :
    (∑ N ∈ EvenIn X H, ‖canonicalExpansion.typeIPart X N‖ ^ 2) ≤ windowUpper X := by
  refine Finset.sum_le_sum ?_
  intro N hN
  exact typeIPart_sq_le_pointwiseUpper X

/--
Any certified bound for the exact Type-I window expression upgrades immediately to the split-side
certificate interface.
-/
theorem zeroModeEnergyBound_of_windowUpper
    {U : ℝ} (hU_nonneg : 0 ≤ U)
    (hUpper :
      ∀ {X : ℕ}, X0 ≤ X →
        windowUpper X ≤
          normFactorSq X * (U / ((H : ℝ) * ((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2))) :
    canonicalExpansion.ZeroModeEnergyBound U := by
  refine ⟨hU_nonneg, ?_⟩
  intro X hX
  exact le_trans (sum_typeIPart_sq_le_windowUpper X) (hUpper hX)

end

end Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundSpec
