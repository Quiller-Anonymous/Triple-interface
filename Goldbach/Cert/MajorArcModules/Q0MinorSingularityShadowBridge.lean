import Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates
import Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors

noncomputable section

/-- Slice-sum of a coefficient object over a chosen finite `t`-support. -/
noncomputable def familySliceSumOn (support : Finset ℤ) (F : ℕ → ℤ → ℂ) : ℕ → ℂ :=
  fun N => ∑ t ∈ support, F N t

/-- Windowed `ℓ²` energy of the slice-sum image under a chosen finite `t`-support. -/
noncomputable def familyWindowSliceEnergyOn
    (window : Finset ℕ) (support : Finset ℤ) (F : ℕ → ℤ → ℂ) : ℝ :=
  ∑ N ∈ window, ‖familySliceSumOn support F N‖ ^ 2

/-- Canonical ambient-support slice sum for a family on the minor window. -/
noncomputable def canonicalAmbientSliceSum (X : ℕ) (F : ℕ → ℤ → ℂ) : ℕ → ℂ :=
  familySliceSumOn (canonicalMinorAmbientSupport X) F

/-- Canonical ambient-support window energy for the slice-sum image of a family. -/
noncomputable def canonicalAmbientWindowSliceEnergy (X : ℕ) (F : ℕ → ℤ → ℂ) : ℝ :=
  familyWindowSliceEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X) F

/-- The exact raw weighted minor slice obtained by summing on the true support `tSupport N`. -/
noncomputable def exactWeightedMinorSlice (X : ℕ) : ℕ → ℂ :=
  fun N => ∑ t ∈ weightedMinorCoeffSupport N, weightedMinorCoeff X N t

/-- The exact windowed slice energy of the raw weighted minor family on its true supports. -/
noncomputable def exactWeightedMinorWindowSliceEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ minorWindow X, ‖exactWeightedMinorSlice X N‖ ^ 2

/-- Canonical ambient slice sum for the exact raw weighted family. -/
noncomputable def weightedMinorCoeffFamilyShadowSlice (X : ℕ) : ℕ → ℂ :=
  canonicalAmbientSliceSum X (weightedMinorCoeffFamily X)

/-- Canonical ambient slice-sum energy for the exact raw weighted family. -/
noncomputable def weightedMinorCoeffFamilyShadowEnergy (X : ℕ) : ℝ :=
  canonicalAmbientWindowSliceEnergy X (weightedMinorCoeffFamily X)

/-- Canonical ambient slice-sum energy for the centered weighted family. -/
noncomputable def coeffCenteredFamilyShadowEnergy (X : ℕ) : ℝ :=
  canonicalAmbientWindowSliceEnergy X (coeffCenteredFamily X)

/-- Canonical ambient slice-sum energy for the weight-regressed arithmetic family. -/
noncomputable def coeffArithFamilyShadowEnergy (X : ℕ) : ℝ :=
  canonicalAmbientWindowSliceEnergy X (coeffArithFamily X)

theorem norm_familySliceSumOn_sq_le_card_mul_coeffNormSqOn
    (support : Finset ℤ) (f : ℤ → ℂ) :
    ‖∑ t ∈ support, f t‖ ^ 2 ≤ (support.card : ℝ) * coeffNormSqOn support f := by
  simpa [coeffNormSqOn, familySliceSumOn] using
    (norm_sum_sq_le_card_mul_sum_norm_sq (s := support) (z := f))

theorem familyWindowSliceEnergyOn_le_card_mul_familyCoeffEnergyOn
    (window : Finset ℕ) (support : Finset ℤ) (F : ℕ → ℤ → ℂ) :
    familyWindowSliceEnergyOn window support F
      ≤
    (support.card : ℝ) * familyCoeffEnergyOn window support F := by
  unfold familyWindowSliceEnergyOn familyCoeffEnergyOn familySliceSumOn coeffNormSqOn
  have hterm :
      ∀ N ∈ window,
        ‖∑ t ∈ support, F N t‖ ^ 2
          ≤
        (support.card : ℝ) * ∑ t ∈ support, ‖F N t‖ ^ 2 := by
    intro N hN
    exact norm_familySliceSumOn_sq_le_card_mul_coeffNormSqOn support (F N)
  have hsum :
      (∑ N ∈ window, ‖∑ t ∈ support, F N t‖ ^ 2)
        ≤
      ∑ N ∈ window, (support.card : ℝ) * ∑ t ∈ support, ‖F N t‖ ^ 2 := by
    exact Finset.sum_le_sum (fun N hN => hterm N hN)
  calc
    (∑ N ∈ window, ‖∑ t ∈ support, F N t‖ ^ 2)
        ≤
      ∑ N ∈ window, (support.card : ℝ) * ∑ t ∈ support, ‖F N t‖ ^ 2 := hsum
    _ = (support.card : ℝ) * ∑ N ∈ window, ∑ t ∈ support, ‖F N t‖ ^ 2 := by
      simp [Finset.mul_sum]

theorem exactWeightedMinorSlice_eq_minorResidual
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ minorWindow X) :
    exactWeightedMinorSlice X N = minorResidual X N TurnkeyRouteQ0.Δ_canon := by
  symm
  simpa [exactWeightedMinorSlice, minorWindow] using
    (minorResidual_eq_sum_weightedMinorCoeff (X := X) (N := N) hX hN)

theorem exactWeightedMinorWindowSliceEnergy_eq_minorResidualWindowEnergy
    {X : ℕ} (hX : X0 ≤ X) :
    exactWeightedMinorWindowSliceEnergy X
      =
    ∑ N ∈ minorWindow X, ‖minorResidual X N TurnkeyRouteQ0.Δ_canon‖ ^ 2 := by
  unfold exactWeightedMinorWindowSliceEnergy
  refine Finset.sum_congr rfl ?_
  intro N hN
  rw [exactWeightedMinorSlice_eq_minorResidual (X := X) (N := N) hX hN]

/-- Canonical ambient slice sum of the approximant attached to a family subspace datum. -/
noncomputable def FamilySubspaceData.shadowApproxSlice
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F) : ℕ → ℂ :=
  canonicalAmbientSliceSum X S.approx

/-- Canonical ambient slice sum of the residual attached to a family subspace datum. -/
noncomputable def FamilySubspaceData.shadowResidualSlice
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F) : ℕ → ℂ :=
  canonicalAmbientSliceSum X S.residual

/-- Canonical ambient window energy of the approximant image. -/
noncomputable def FamilySubspaceData.shadowApproxEnergy
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F) : ℝ :=
  canonicalAmbientWindowSliceEnergy X S.approx

/-- Canonical ambient window energy of the residual image. -/
noncomputable def FamilySubspaceData.shadowResidualEnergy
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F) : ℝ :=
  canonicalAmbientWindowSliceEnergy X S.residual

theorem FamilySubspaceData.familySlice_eq_approx_add_residual
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F)
    (support : Finset ℤ) (N : ℕ) :
    familySliceSumOn support F N
      =
    familySliceSumOn support S.approx N + familySliceSumOn support S.residual N := by
  unfold familySliceSumOn
  calc
    ∑ t ∈ support, F N t
        = ∑ t ∈ support, (S.approx N t + S.residual N t) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rw [← S.family_eq_approx_add_residual N t]
    _ = (∑ t ∈ support, S.approx N t) + ∑ t ∈ support, S.residual N t := by
          rw [Finset.sum_add_distrib]

/-- Packaged downstream residual upper envelope on the canonical ambient support. -/
noncomputable def FamilySubspaceCertificate.shadowResidualUpper
    {X : ℕ} {F : ℕ → ℤ → ℂ} (C : FamilySubspaceCertificate X F) : ℝ :=
  ((canonicalMinorAmbientSupport X).card : ℝ) * C.residualUpper

theorem FamilySubspaceCertificate.shadowResidualEnergy_le
    {X : ℕ} {F : ℕ → ℤ → ℂ} (C : FamilySubspaceCertificate X F) :
    FamilySubspaceData.shadowResidualEnergy C.toFamilySubspaceData
      ≤ FamilySubspaceCertificate.shadowResidualUpper C := by
  unfold FamilySubspaceData.shadowResidualEnergy FamilySubspaceCertificate.shadowResidualUpper
  have hshadow :
      canonicalAmbientWindowSliceEnergy X C.toFamilySubspaceData.residual
        ≤
      ((canonicalMinorAmbientSupport X).card : ℝ)
        * familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
            C.toFamilySubspaceData.residual := by
    exact familyWindowSliceEnergyOn_le_card_mul_familyCoeffEnergyOn
      (minorWindow X) (canonicalMinorAmbientSupport X) C.toFamilySubspaceData.residual
  exact le_trans hshadow (mul_le_mul_of_nonneg_left C.residualEnergy_le (by positivity))

/-- Downstream canonical ambient residual energy for the exact raw weighted family certificate. -/
noncomputable def WeightedMinorCoeffFamilyCertificate.shadowResidualEnergy
    {X : ℕ} (C : WeightedMinorCoeffFamilyCertificate X) : ℝ :=
  FamilySubspaceData.shadowResidualEnergy C.toFamilySubspaceData

/-- Downstream canonical ambient residual energy for the centered-family certificate. -/
noncomputable def CoeffCenteredFamilyCertificate.shadowResidualEnergy
    {X : ℕ} (C : CoeffCenteredFamilyCertificate X) : ℝ :=
  FamilySubspaceData.shadowResidualEnergy C.toFamilySubspaceData

/-- Downstream canonical ambient residual energy for the arithmetic-family certificate. -/
noncomputable def CoeffArithFamilyCertificate.shadowResidualEnergy
    {X : ℕ} (C : CoeffArithFamilyCertificate X) : ℝ :=
  FamilySubspaceData.shadowResidualEnergy C.toFamilySubspaceData

theorem weightedMinorCoeffFamilyShadowEnergy_le_card_mul_familyCoeffEnergy
    (X : ℕ) :
    weightedMinorCoeffFamilyShadowEnergy X
      ≤
    ((canonicalMinorAmbientSupport X).card : ℝ)
      * familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
          (weightedMinorCoeffFamily X) := by
  exact familyWindowSliceEnergyOn_le_card_mul_familyCoeffEnergyOn
    (minorWindow X) (canonicalMinorAmbientSupport X) (weightedMinorCoeffFamily X)

theorem coeffCenteredFamilyShadowEnergy_le_card_mul_familyEnergy
    (X : ℕ) :
    coeffCenteredFamilyShadowEnergy X
      ≤
    ((canonicalMinorAmbientSupport X).card : ℝ) * coeffCenteredFamilyEnergy X := by
  unfold coeffCenteredFamilyShadowEnergy coeffCenteredFamilyEnergy
  exact familyWindowSliceEnergyOn_le_card_mul_familyCoeffEnergyOn
    (minorWindow X) (canonicalMinorAmbientSupport X) (coeffCenteredFamily X)

theorem coeffArithFamilyShadowEnergy_le_card_mul_familyEnergy
    (X : ℕ) :
    coeffArithFamilyShadowEnergy X
      ≤
    ((canonicalMinorAmbientSupport X).card : ℝ) * coeffArithFamilyEnergy X := by
  unfold coeffArithFamilyShadowEnergy coeffArithFamilyEnergy
  exact familyWindowSliceEnergyOn_le_card_mul_familyCoeffEnergyOn
    (minorWindow X) (canonicalMinorAmbientSupport X) (coeffArithFamily X)

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
