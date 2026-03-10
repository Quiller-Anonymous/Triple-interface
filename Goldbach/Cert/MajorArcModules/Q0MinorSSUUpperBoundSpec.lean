import Goldbach.Cert.MajorArcModules.Q0MinorSSUFourierDecomp

/-!
Generator-facing window-sum upper-bound target for the ε₁ SSU / nonzero-mode piece.

The deterministic TT* reduction already proves a pointwise bound for `canonicalExpansion.ssuPart`.
This file packages the exact finite window sum that remains to be evaluated numerically. Once a
generator certifies that window sum against a constant `U`, Lean upgrades it to
`canonicalExpansion.NonzeroModeEnergyBound U`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundSpec

open scoped BigOperators Interval

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorSSUFourierDecomp
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- Pointwise deterministic SSU upper bound produced by the current minor TT* reduction. -/
noncomputable def pointwiseUpper (X N : ℕ) : ℝ :=
  ‖q0NormFactor N‖ ^ 2 *
    (2 *
      ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
        +
      (4 * kernelMassNZOdd X Δ_canon N) * (aTerm2Mass X) * (coeffMass X N)
        +
      (3 * ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2) * (diagMass X N)))

/-- Exact SSU window expression that the generator is expected to upper-bound. -/
noncomputable def windowUpper (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, pointwiseUpper X N

lemma ssuPart_sq_le_pointwiseUpper {X N : ℕ} (hN : N ∈ EvenIn X H) :
    ‖canonicalExpansion.ssuPart X N‖ ^ 2 ≤ pointwiseUpper X N := by
  have hEvenN : Even N := Goldbach.Windows.even_of_isEven (Finset.mem_filter.mp hN).2
  simpa [pointwiseUpper] using
    ssuPart_norm_sq_le_public_parity_bound (X := X) (N := N) hEvenN

theorem sum_ssuPart_sq_le_windowUpper (X : ℕ) :
    (∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N‖ ^ 2) ≤ windowUpper X := by
  refine Finset.sum_le_sum ?_
  intro N hN
  exact ssuPart_sq_le_pointwiseUpper (X := X) hN

/--
Any certified bound for the exact SSU window expression upgrades immediately to the split-side
certificate interface.
-/
theorem nonzeroModeEnergyBound_of_windowUpper
    {U : ℝ} (hU_nonneg : 0 ≤ U)
    (hUpper :
      ∀ {X : ℕ}, X0 ≤ X →
        windowUpper X ≤ normFactorSq X * (U * ((H : ℝ) / (X : ℝ)))) :
    canonicalExpansion.NonzeroModeEnergyBound U := by
  refine ⟨hU_nonneg, ?_⟩
  intro X hX
  exact le_trans (sum_ssuPart_sq_le_windowUpper X) (hUpper hX)

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundSpec
