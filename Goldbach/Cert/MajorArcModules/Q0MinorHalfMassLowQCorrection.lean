import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowQCorrection

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.Cert.MajorArcModules.Q0MinorTrueSigmaBridge
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTrueTail

noncomputable section

/-- First explicit low-`q` cutoff suggested by the canonical-normalization diagnostics. -/
def lowQCutoff : ℕ := 30

/--
The canonically normalized finite-truncation combination on the true Ramanujan seam.

This is the exact object whose low-`q` variation is now the live arithmetic frontier.
-/
noncomputable def canonicalRawHalfMassSeriesTruncCombination (X N : ℕ) : ℂ :=
  rawHalfMassTrueSeriesCorrection ramanujanSeriesOnWindow X N + canonicalNormalizedSigmaTruncQ0 N

/-- The explicit low-`q` correction extracted from the canonically normalized truncation. -/
noncomputable def canonicalLowQCorrection (N : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) lowQCutoff, canonicalNormalizedSigmaTruncSummand q N

/--
Residual after removing the explicit low-`q` correction from the canonically normalized finite
truncation combination.
-/
noncomputable def canonicalHighQResidual (X N : ℕ) : ℂ :=
  canonicalRawHalfMassSeriesTruncCombination X N - canonicalLowQCorrection N

theorem canonicalRawHalfMassSeriesTruncCombination_eq_rawHalfMassSeriesTruncCombination_ramanujan
    (X N : ℕ) :
    canonicalRawHalfMassSeriesTruncCombination X N
      =
    rawHalfMassSeriesTruncCombination ramanujanSeriesOnWindow X N := by
  unfold canonicalRawHalfMassSeriesTruncCombination rawHalfMassSeriesTruncCombination
  rw [canonicalNormalizedSigmaTruncQ0_eq_normalizedSigmaTruncQ0_ramanujanSeriesOnWindow]

theorem canonicalHighQResidual_eq_sub
    (X N : ℕ) :
    canonicalHighQResidual X N
      =
    canonicalRawHalfMassSeriesTruncCombination X N - canonicalLowQCorrection N := by
  rfl

theorem canonicalRawHalfMassSeriesTruncCombination_eq_lowQCorrection_add_highQResidual
    (X N : ℕ) :
    canonicalRawHalfMassSeriesTruncCombination X N
      =
    canonicalLowQCorrection N + canonicalHighQResidual X N := by
  unfold canonicalHighQResidual
  ring

/-- Raw window sum of the explicit low-`q` correction on the canonical even window. -/
noncomputable def canonicalLowQCorrectionWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, canonicalLowQCorrection N

/-- Raw window sum of the high-`q` residual on the canonical even window. -/
noncomputable def canonicalHighQResidualWindowRawSum (X : ℕ) : ℂ :=
  ∑ N ∈ EvenIn X H, canonicalHighQResidual X N

/-- Canonical even-window average of the explicit low-`q` correction. -/
noncomputable def canonicalLowQCorrectionWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * canonicalLowQCorrectionWindowRawSum X

/-- Canonical even-window average of the high-`q` residual. -/
noncomputable def canonicalHighQResidualWindowAverage (X : ℕ) : ℂ :=
  ((EvenIn X H).card : ℂ)⁻¹ * canonicalHighQResidualWindowRawSum X

/-- Centered explicit low-`q` correction on the canonical even window. -/
noncomputable def centeredCanonicalLowQCorrection (X N : ℕ) : ℂ :=
  canonicalLowQCorrection N - canonicalLowQCorrectionWindowAverage X

/-- Centered high-`q` residual on the canonical even window. -/
noncomputable def centeredCanonicalHighQResidual (X N : ℕ) : ℂ :=
  canonicalHighQResidual X N - canonicalHighQResidualWindowAverage X

/-- Centered canonically normalized finite-truncation combination on the canonical even window. -/
noncomputable def centeredCanonicalRawHalfMassSeriesTruncCombination (X N : ℕ) : ℂ :=
  canonicalRawHalfMassSeriesTruncCombination X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, canonicalRawHalfMassSeriesTruncCombination X M

theorem centeredCanonicalRawHalfMassSeriesTruncCombination_eq_lowQ_add_highQ
    (X N : ℕ) :
    centeredCanonicalRawHalfMassSeriesTruncCombination X N
      =
    centeredCanonicalLowQCorrection X N + centeredCanonicalHighQResidual X N := by
  unfold centeredCanonicalRawHalfMassSeriesTruncCombination
    centeredCanonicalLowQCorrection centeredCanonicalHighQResidual
    canonicalLowQCorrectionWindowAverage canonicalHighQResidualWindowAverage
    canonicalLowQCorrectionWindowRawSum canonicalHighQResidualWindowRawSum
  rw [show (∑ M ∈ EvenIn X H, canonicalRawHalfMassSeriesTruncCombination X M)
      =
    (∑ M ∈ EvenIn X H, canonicalLowQCorrection M)
      + ∑ M ∈ EvenIn X H, canonicalHighQResidual X M by
        calc
          ∑ M ∈ EvenIn X H, canonicalRawHalfMassSeriesTruncCombination X M
              =
            ∑ M ∈ EvenIn X H, (canonicalLowQCorrection M + canonicalHighQResidual X M) := by
              refine Finset.sum_congr rfl ?_
              intro M hM
              rw [canonicalRawHalfMassSeriesTruncCombination_eq_lowQCorrection_add_highQResidual]
          _ =
            (∑ M ∈ EvenIn X H, canonicalLowQCorrection M)
              + ∑ M ∈ EvenIn X H, canonicalHighQResidual X M := by
                rw [Finset.sum_add_distrib]]
  rw [mul_add]
  rw [canonicalRawHalfMassSeriesTruncCombination_eq_lowQCorrection_add_highQResidual]
  ring_nf

/-- Squared `ℓ²(EvenIn X H)` energy of the centered explicit low-`q` correction. -/
noncomputable def centeredCanonicalLowQCorrectionWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalLowQCorrection X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the centered canonically normalized combination. -/
noncomputable def centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalRawHalfMassSeriesTruncCombination X N‖ ^ 2

/-- Squared `ℓ²(EvenIn X H)` energy of the centered high-`q` residual. -/
noncomputable def centeredCanonicalHighQResidualWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalHighQResidual X N‖ ^ 2

/-- Pointwise quadratic upper bound used to combine the low-`q` and high-`q` centered pieces. -/
noncomputable def centeredCanonicalLowHighUpper (X N : ℕ) : ℝ :=
  2 * ‖centeredCanonicalLowQCorrection X N‖ ^ 2
    + 2 * ‖centeredCanonicalHighQResidual X N‖ ^ 2

private theorem centeredCanonicalRawHalfMassSeriesTruncCombination_sq_le
    (X N : ℕ) :
    ‖centeredCanonicalRawHalfMassSeriesTruncCombination X N‖ ^ 2
      ≤
    centeredCanonicalLowHighUpper X N := by
  rw [centeredCanonicalRawHalfMassSeriesTruncCombination_eq_lowQ_add_highQ]
  unfold centeredCanonicalLowHighUpper
  have hnorm :=
    norm_add_le (centeredCanonicalLowQCorrection X N) (centeredCanonicalHighQResidual X N)
  have hlu : 0 ≤ ‖centeredCanonicalLowQCorrection X N‖ := norm_nonneg _
  have hlv : 0 ≤ ‖centeredCanonicalHighQResidual X N‖ := norm_nonneg _
  have hlhs : 0 ≤ ‖centeredCanonicalLowQCorrection X N + centeredCanonicalHighQResidual X N‖ :=
    norm_nonneg _
  have hsq1 :
      ‖centeredCanonicalLowQCorrection X N + centeredCanonicalHighQResidual X N‖ ^ 2
        ≤
      (‖centeredCanonicalLowQCorrection X N‖ + ‖centeredCanonicalHighQResidual X N‖) ^ 2 := by
    nlinarith
  have hsq2 :
      (‖centeredCanonicalLowQCorrection X N‖ + ‖centeredCanonicalHighQResidual X N‖) ^ 2
        ≤
      2 * ‖centeredCanonicalLowQCorrection X N‖ ^ 2
        + 2 * ‖centeredCanonicalHighQResidual X N‖ ^ 2 := by
    have hnonneg :
        0 ≤ (‖centeredCanonicalLowQCorrection X N‖ - ‖centeredCanonicalHighQResidual X N‖) ^ 2 :=
      sq_nonneg _
    nlinarith
  exact le_trans hsq1 hsq2

theorem centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy_le_sum_upper
    (X : ℕ) :
    centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy X
      ≤
    ∑ N ∈ EvenIn X H, centeredCanonicalLowHighUpper X N := by
  unfold centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy
  exact Finset.sum_le_sum (fun N hN =>
    centeredCanonicalRawHalfMassSeriesTruncCombination_sq_le X N)

theorem sum_centeredCanonicalLowHighUpper_eq
    (X : ℕ) :
    (∑ N ∈ EvenIn X H, centeredCanonicalLowHighUpper X N)
      =
    2 * centeredCanonicalLowQCorrectionWindowEnergy X
      + 2 * centeredCanonicalHighQResidualWindowEnergy X := by
  unfold centeredCanonicalLowHighUpper centeredCanonicalLowQCorrectionWindowEnergy
    centeredCanonicalHighQResidualWindowEnergy
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]

theorem centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy_le
    (X : ℕ) :
    centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy X
      ≤
    2 * centeredCanonicalLowQCorrectionWindowEnergy X
      + 2 * centeredCanonicalHighQResidualWindowEnergy X := by
  calc
    centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy X
        ≤
      ∑ N ∈ EvenIn X H, centeredCanonicalLowHighUpper X N :=
      centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy_le_sum_upper X
    _ =
      2 * centeredCanonicalLowQCorrectionWindowEnergy X
        + 2 * centeredCanonicalHighQResidualWindowEnergy X :=
      sum_centeredCanonicalLowHighUpper_eq X

/--
The centered low-`q` correction target after extracting the explicit `q ≤ 30` piece from the
canonically normalized finite-truncation combination.
-/
structure CenteredCanonicalLowQCorrectionWindowTarget (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalLowQCorrectionWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Combined centered target for the canonically normalized finite-truncation combination after
splitting into the explicit low-`q` correction and the high-`q` residual.
-/
structure CenteredCanonicalRawHalfMassSeriesTruncCombinationWindowTarget (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
The centered high-`q` residual target after removing the explicit `q ≤ 30` correction from the
canonically normalized finite-truncation combination.
-/
structure CenteredCanonicalHighQResidualWindowTarget (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalHighQResidualWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

theorem centeredCanonicalRawHalfMassSeriesTruncCombinationWindowTarget_of_lowQ_and_highQ
    {C3low C3high : ℝ}
    (hLow : CenteredCanonicalLowQCorrectionWindowTarget C3low)
    (hHigh : CenteredCanonicalHighQResidualWindowTarget C3high) :
    CenteredCanonicalRawHalfMassSeriesTruncCombinationWindowTarget (2 * C3low + 2 * C3high) := by
  refine ⟨by nlinarith [hLow.C3_nonneg, hHigh.C3_nonneg], ?_⟩
  intro X hX
  have hLowX := hLow.bound hX
  have hHighX := hHigh.bound hX
  calc
    centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy X
        ≤
      2 * centeredCanonicalLowQCorrectionWindowEnergy X
        + 2 * centeredCanonicalHighQResidualWindowEnergy X :=
      centeredCanonicalRawHalfMassSeriesTruncCombinationWindowEnergy_le X
    _ ≤
      2 * (C3low / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))
        + 2 * (C3high / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
      nlinarith
    _ =
      (2 * C3low + 2 * C3high)
        / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
      ring

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowQCorrection
