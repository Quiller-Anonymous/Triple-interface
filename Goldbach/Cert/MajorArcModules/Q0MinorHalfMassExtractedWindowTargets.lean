import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowRankMainTerm

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassExtractedWindowTargets

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.BankPieces.Cert.RawScaleSmallBetaS7Decomposition
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowRankMainTerm

noncomputable section

/-- Centered low-modulus extracted remainder supported on the `S7 \ core5` block. -/
noncomputable def centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock
    (X N : ℕ) : ℂ :=
  canonicalExplicitExtractedSecondaryLowRemainderBlock X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, canonicalExplicitExtractedSecondaryLowRemainderBlock X M

/-- Centered extracted remainder supported on moduli outside `S7`. -/
noncomputable def centeredCanonicalExplicitExtractedBeyondS7Remainder
    (X N : ℕ) : ℂ :=
  smallBetaSecondaryBeyondS7MainTermC X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, smallBetaSecondaryBeyondS7MainTermC X M

/-- Window energy of the centered low-modulus extracted remainder block. -/
noncomputable def centeredCanonicalExplicitExtractedSecondaryLowRemainderBlockWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N‖ ^ 2

/-- Window energy of the centered beyond-`S7` extracted remainder block. -/
noncomputable def centeredCanonicalExplicitExtractedBeyondS7RemainderWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalExplicitExtractedBeyondS7Remainder X N‖ ^ 2

/-- Local centered alias for the extracted post-core5 remainder. -/
noncomputable def centeredCanonicalExplicitExtractedPostCore5RemainderAux
    (X N : ℕ) : ℂ :=
  canonicalExplicitExtractedPostCore5Remainder X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, canonicalExplicitExtractedPostCore5Remainder X M

/-- Local window energy for the centered extracted post-core5 remainder. -/
noncomputable def centeredCanonicalExplicitExtractedPostCore5RemainderAuxWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalExplicitExtractedPostCore5RemainderAux X N‖ ^ 2

theorem centeredCanonicalExplicitExtractedPostCore5RemainderAux_eq_lowRemainder_add_beyondS7
    (X N : ℕ) (hX : 2 ≤ X) :
    centeredCanonicalExplicitExtractedPostCore5RemainderAux X N
      =
    centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N
      + centeredCanonicalExplicitExtractedBeyondS7Remainder X N := by
  unfold centeredCanonicalExplicitExtractedPostCore5RemainderAux
    centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock
    centeredCanonicalExplicitExtractedBeyondS7Remainder
  rw [canonicalExplicitExtractedPostCore5Remainder_eq_lowRemainder_add_beyondS7 (X := X) (N := N) hX]
  have hsum :
      ∑ M ∈ EvenIn X H, canonicalExplicitExtractedPostCore5Remainder X M
        =
      ∑ M ∈ EvenIn X H,
        (canonicalExplicitExtractedSecondaryLowRemainderBlock X M
          + smallBetaSecondaryBeyondS7MainTermC X M) := by
    refine Finset.sum_congr rfl ?_
    intro M hM
    rw [canonicalExplicitExtractedPostCore5Remainder_eq_lowRemainder_add_beyondS7 (X := X) (N := M) hX]
  rw [hsum, Finset.sum_add_distrib]
  ring

/-- Pointwise quadratic upper bound for the extracted post-core5 remainder split. -/
noncomputable def canonicalExplicitExtractedPostCore5RemainderUpper
    (X N : ℕ) : ℝ :=
  2 * ‖centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N‖ ^ 2
    + 2 * ‖centeredCanonicalExplicitExtractedBeyondS7Remainder X N‖ ^ 2

private theorem centeredCanonicalExplicitExtractedPostCore5Remainder_sq_le
    (X N : ℕ) (hX : 2 ≤ X) :
    ‖centeredCanonicalExplicitExtractedPostCore5RemainderAux X N‖ ^ 2
      ≤
    canonicalExplicitExtractedPostCore5RemainderUpper X N := by
  rw [centeredCanonicalExplicitExtractedPostCore5RemainderAux_eq_lowRemainder_add_beyondS7
    (X := X) (N := N) hX]
  unfold canonicalExplicitExtractedPostCore5RemainderUpper
  have hnorm :=
    norm_add_le
      (centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N)
      (centeredCanonicalExplicitExtractedBeyondS7Remainder X N)
  have hsq1 :
      ‖centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N
          + centeredCanonicalExplicitExtractedBeyondS7Remainder X N‖ ^ 2
        ≤
      (‖centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N‖
          + ‖centeredCanonicalExplicitExtractedBeyondS7Remainder X N‖) ^ 2 := by
    nlinarith [hnorm,
      norm_nonneg (centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N),
      norm_nonneg (centeredCanonicalExplicitExtractedBeyondS7Remainder X N),
      norm_nonneg
        (centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N
          + centeredCanonicalExplicitExtractedBeyondS7Remainder X N)]
  have hsq2 :
      (‖centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N‖
          + ‖centeredCanonicalExplicitExtractedBeyondS7Remainder X N‖) ^ 2
        ≤
      2 * ‖centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N‖ ^ 2
        + 2 * ‖centeredCanonicalExplicitExtractedBeyondS7Remainder X N‖ ^ 2 := by
    have hnonneg :
        0 ≤
          (‖centeredCanonicalExplicitExtractedSecondaryLowRemainderBlock X N‖
            - ‖centeredCanonicalExplicitExtractedBeyondS7Remainder X N‖) ^ 2 := by
      exact sq_nonneg _
    nlinarith
  exact le_trans hsq1 hsq2

theorem centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy_le
    (X : ℕ) (hX : 2 ≤ X) :
    centeredCanonicalExplicitExtractedPostCore5RemainderAuxWindowEnergy X
      ≤
    2 * centeredCanonicalExplicitExtractedSecondaryLowRemainderBlockWindowEnergy X
      + 2 * centeredCanonicalExplicitExtractedBeyondS7RemainderWindowEnergy X := by
  calc
    centeredCanonicalExplicitExtractedPostCore5RemainderAuxWindowEnergy X
        ≤
      ∑ N ∈ EvenIn X H, canonicalExplicitExtractedPostCore5RemainderUpper X N := by
            unfold centeredCanonicalExplicitExtractedPostCore5RemainderAuxWindowEnergy
            exact Finset.sum_le_sum (fun N hN =>
              centeredCanonicalExplicitExtractedPostCore5Remainder_sq_le X N hX)
    _ =
      2 * centeredCanonicalExplicitExtractedSecondaryLowRemainderBlockWindowEnergy X
        + 2 * centeredCanonicalExplicitExtractedBeyondS7RemainderWindowEnergy X := by
          unfold canonicalExplicitExtractedPostCore5RemainderUpper
            centeredCanonicalExplicitExtractedSecondaryLowRemainderBlockWindowEnergy
            centeredCanonicalExplicitExtractedBeyondS7RemainderWindowEnergy
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Route-sized target for the centered low-modulus extracted remainder block. -/
structure CenteredCanonicalExplicitExtractedSecondaryLowRemainderBlockWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalExplicitExtractedSecondaryLowRemainderBlockWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/-- Route-sized target for the centered beyond-`S7` extracted remainder block. -/
structure CenteredCanonicalExplicitExtractedBeyondS7RemainderWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalExplicitExtractedBeyondS7RemainderWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

theorem centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy_bound_of_low_and_beyond
    {CLow CBeyond : ℝ}
    (hLow : CenteredCanonicalExplicitExtractedSecondaryLowRemainderBlockWindowTarget CLow)
    (hBeyond : CenteredCanonicalExplicitExtractedBeyondS7RemainderWindowTarget CBeyond)
    {X : ℕ} (hX0 : X0 ≤ X) :
    centeredCanonicalExplicitExtractedPostCore5RemainderAuxWindowEnergy X
      ≤
    (2 * CLow + 2 * CBeyond)
      / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
  have hX : 2 ≤ X := le_trans (by decide : 2 ≤ X0) hX0
  have hmain := centeredCanonicalExplicitExtractedPostCore5RemainderWindowEnergy_le X hX
  have hL := hLow.bound hX0
  have hB := hBeyond.bound hX0
  calc
    centeredCanonicalExplicitExtractedPostCore5RemainderAuxWindowEnergy X
        ≤
      2 * centeredCanonicalExplicitExtractedSecondaryLowRemainderBlockWindowEnergy X
        + 2 * centeredCanonicalExplicitExtractedBeyondS7RemainderWindowEnergy X := hmain
    _ ≤
      2 * (CLow / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))
        + 2 * (CBeyond / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
          gcongr
    _ =
      (2 * CLow + 2 * CBeyond)
        / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
          field_simp

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassExtractedWindowTargets
