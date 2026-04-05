import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowRankMainTerm
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassExtractedWindowTargets
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassResidualWindowTargets

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowRankMainTerm
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassExtractedWindowTargets
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets

noncomputable section

/-- Centered extracted post-core5 remainder on the canonical even window. -/
noncomputable def centeredCanonicalExplicitExtractedPostCore5Remainder
    (X N : ℕ) : ℂ :=
  canonicalExplicitExtractedPostCore5Remainder X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, canonicalExplicitExtractedPostCore5Remainder X M

/-- Centered corrected freeze discrepancy on the canonical even window. -/
noncomputable def centeredCanonicalCorrectedFreezeDiscrepancy
    (X N : ℕ) : ℂ :=
  canonicalCorrectedFreezeDiscrepancy X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, canonicalCorrectedFreezeDiscrepancy X M

/-- Squared `ℓ²(EvenIn X H)` energy of the centered extracted post-core5 remainder. -/
noncomputable def centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalExplicitExtractedPostCore5Remainder X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the centered corrected freeze discrepancy. -/
noncomputable def centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalCorrectedFreezeDiscrepancy X N‖ ^ 2

/--
Exact centered decomposition hypothesis for the live post-core5 residual.

This is the theorem-facing seam needed to reduce the residual-energy problem to the two exact
remainder blocks already exposed in `Q0MinorHalfMassLowRankMainTerm`.
-/
structure CanonicalSigmaScaleExtractedCore5ResidualDecomposition
    (coeff : ℕ → Fin 11 → ℂ) : Prop where
  eq_add :
    ∀ X N,
      canonicalSigmaScaleExtractedCore5Residual coeff X N
        =
      centeredCanonicalExplicitExtractedPostCore5Remainder X N
        + centeredCanonicalCorrectedFreezeDiscrepancy X N

/-- Pointwise quadratic upper bound used to combine the two exact remainder blocks. -/
noncomputable def canonicalSigmaScaleExtractedCore5ResidualUpper
    (X N : ℕ) : ℝ :=
  2 * ‖centeredCanonicalExplicitExtractedPostCore5Remainder X N‖ ^ 2
    + 2 * ‖centeredCanonicalCorrectedFreezeDiscrepancy X N‖ ^ 2

private theorem canonicalSigmaScaleExtractedCore5Residual_sq_le
    (coeff : ℕ → Fin 11 → ℂ)
    (hDecomp : CanonicalSigmaScaleExtractedCore5ResidualDecomposition coeff)
    (X N : ℕ) :
    ‖canonicalSigmaScaleExtractedCore5Residual coeff X N‖ ^ 2
      ≤
    canonicalSigmaScaleExtractedCore5ResidualUpper X N := by
  rw [hDecomp.eq_add X N]
  unfold canonicalSigmaScaleExtractedCore5ResidualUpper
  have hnorm :=
    norm_add_le
      (centeredCanonicalExplicitExtractedPostCore5Remainder X N)
      (centeredCanonicalCorrectedFreezeDiscrepancy X N)
  have hsq1 :
      ‖centeredCanonicalExplicitExtractedPostCore5Remainder X N
          + centeredCanonicalCorrectedFreezeDiscrepancy X N‖ ^ 2
        ≤
      (‖centeredCanonicalExplicitExtractedPostCore5Remainder X N‖
          + ‖centeredCanonicalCorrectedFreezeDiscrepancy X N‖) ^ 2 := by
    nlinarith [hnorm, norm_nonneg (centeredCanonicalExplicitExtractedPostCore5Remainder X N),
      norm_nonneg (centeredCanonicalCorrectedFreezeDiscrepancy X N),
      norm_nonneg (centeredCanonicalExplicitExtractedPostCore5Remainder X N
        + centeredCanonicalCorrectedFreezeDiscrepancy X N)]
  have hsq2 :
      (‖centeredCanonicalExplicitExtractedPostCore5Remainder X N‖
          + ‖centeredCanonicalCorrectedFreezeDiscrepancy X N‖) ^ 2
        ≤
      2 * ‖centeredCanonicalExplicitExtractedPostCore5Remainder X N‖ ^ 2
        + 2 * ‖centeredCanonicalCorrectedFreezeDiscrepancy X N‖ ^ 2 := by
    have hnonneg :
        0 ≤
          (‖centeredCanonicalExplicitExtractedPostCore5Remainder X N‖
            - ‖centeredCanonicalCorrectedFreezeDiscrepancy X N‖) ^ 2 := by
      exact sq_nonneg _
    nlinarith
  exact le_trans hsq1 hsq2

theorem canonicalSigmaScaleExtractedCore5ResidualWindowEnergy_le_sum_upper
    (coeff : ℕ → Fin 11 → ℂ)
    (hDecomp : CanonicalSigmaScaleExtractedCore5ResidualDecomposition coeff)
    (X : ℕ) :
    canonicalSigmaScaleExtractedCore5ResidualWindowEnergy coeff X
      ≤
    ∑ N ∈ EvenIn X H, canonicalSigmaScaleExtractedCore5ResidualUpper X N := by
  unfold canonicalSigmaScaleExtractedCore5ResidualWindowEnergy
  exact Finset.sum_le_sum (fun N hN =>
    canonicalSigmaScaleExtractedCore5Residual_sq_le coeff hDecomp X N)

theorem sum_canonicalSigmaScaleExtractedCore5ResidualUpper_eq
    (X : ℕ) :
    (∑ N ∈ EvenIn X H, canonicalSigmaScaleExtractedCore5ResidualUpper X N)
      =
    2 * centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy X
      + 2 * centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy X := by
  unfold canonicalSigmaScaleExtractedCore5ResidualUpper
    centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy
    centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]

theorem canonicalSigmaScaleExtractedCore5ResidualWindowEnergy_le
    (coeff : ℕ → Fin 11 → ℂ)
    (hDecomp : CanonicalSigmaScaleExtractedCore5ResidualDecomposition coeff)
    (X : ℕ) :
    canonicalSigmaScaleExtractedCore5ResidualWindowEnergy coeff X
      ≤
    2 * centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy X
      + 2 * centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy X := by
  calc
    canonicalSigmaScaleExtractedCore5ResidualWindowEnergy coeff X
        ≤
      ∑ N ∈ EvenIn X H, canonicalSigmaScaleExtractedCore5ResidualUpper X N :=
      canonicalSigmaScaleExtractedCore5ResidualWindowEnergy_le_sum_upper coeff hDecomp X
    _ =
      2 * centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy X
        + 2 * centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy X :=
      sum_canonicalSigmaScaleExtractedCore5ResidualUpper_eq X

/-- Route-sized target for the centered extracted post-core5 remainder. -/
structure CenteredCanonicalExplicitExtractedPostCore5RemainderWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/-- Route-sized target for the centered corrected freeze discrepancy. -/
structure CenteredCanonicalCorrectedFreezeDiscrepancyWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

theorem centeredCanonicalExplicitExtractedPostCore5RemainderWindowTarget_of_low_and_beyond
    {CLow CBeyond : ℝ}
    (hLow : CenteredCanonicalExplicitExtractedSecondaryLowRemainderBlockWindowTarget CLow)
    (hBeyond : CenteredCanonicalExplicitExtractedBeyondS7RemainderWindowTarget CBeyond) :
    CenteredCanonicalExplicitExtractedPostCore5RemainderWindowTarget (2 * CLow + 2 * CBeyond) where
  C3_nonneg := by
    nlinarith [hLow.C3_nonneg, hBeyond.C3_nonneg]
  bound := by
    intro X hX
    simpa [centeredCanonicalExplicitExtractedPostCore5RemainderAuxWindowEnergy,
      centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy] using
      centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy_bound_of_low_and_beyond
        hLow hBeyond hX

theorem centeredCanonicalCorrectedFreezeDiscrepancyWindowTarget_of_q1_and_weightedGe2
    {CQ1 CGe2 : ℝ}
    (hQ1 : CenteredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowTarget CQ1)
    (hGe2 : CenteredCanonicalCorrectedFreezeWeightedGe2DefectWindowTarget CGe2) :
    CenteredCanonicalCorrectedFreezeDiscrepancyWindowTarget (2 * CQ1 + 2 * CGe2) where
  C3_nonneg := by
    nlinarith [hQ1.C3_nonneg, hGe2.C3_nonneg]
  bound := by
    intro X hX
    simpa [centeredCanonicalCorrectedFreezeDiscrepancyAuxWindowEnergy,
      centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy] using
      centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy_bound_of_q1_and_weightedGe2
        hQ1 hGe2 hX

theorem centeredCanonicalSigmaScaleExtractedCore5ResidualWindowTarget_of_extracted_and_freeze
    (coeff : ℕ → Fin 11 → ℂ)
    (hDecomp : CanonicalSigmaScaleExtractedCore5ResidualDecomposition coeff)
    {CExtracted CFreeze : ℝ}
    (hExtracted : CenteredCanonicalExplicitExtractedPostCore5RemainderWindowTarget CExtracted)
    (hFreeze : CenteredCanonicalCorrectedFreezeDiscrepancyWindowTarget CFreeze) :
    CenteredCanonicalSigmaScaleExtractedCore5ResidualWindowTarget coeff
      (2 * CExtracted + 2 * CFreeze) where
  C3_nonneg := by
    nlinarith [hExtracted.C3_nonneg, hFreeze.C3_nonneg]
  bound := by
    intro X hX
    have hmain := canonicalSigmaScaleExtractedCore5ResidualWindowEnergy_le coeff hDecomp X
    have hE := hExtracted.bound hX
    have hF := hFreeze.bound hX
    calc
      canonicalSigmaScaleExtractedCore5ResidualWindowEnergy coeff X
          ≤
        2 * centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy X
          + 2 * centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy X := hmain
      _ ≤
        2 * (CExtracted / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))
          + 2 * (CFreeze / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
            gcongr
      _ =
        (2 * CExtracted + 2 * CFreeze)
          / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
            field_simp

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassResidualWindowTargets
