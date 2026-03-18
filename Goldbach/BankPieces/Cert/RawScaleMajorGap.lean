import Goldbach.BankPieces.Cert.RawScaleClosureGate
import Goldbach.BankPieces.Cert.ProjectedTrueFromQ0
import Goldbach.Cert.CanonLogBounds
import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
import Goldbach.Cert.MajorArcModules.CorrModel

namespace Goldbach.BankPieces.Cert.RawScaleMajorGap

open Complex
open Goldbach
open Goldbach.Windows
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit

noncomputable section

private lemma weight_mass_pos_of_X0_le {X : ℕ} (hX : BankParams.X0 ≤ X) :
    0 < Goldbach.AO_WeightMass.weight_mass X := by
  have hlog_ge : (10 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    linarith
  have hden_pos : 0 < Real.log (X : ℝ) * (2 * (BankParams.H : ℝ) + 1) := by
    positivity
  have hwScale_pos : 0 < Goldbach.BG_Bank.wScale X := by
    dsimp [Goldbach.BG_Bank.wScale]
    exact one_div_pos.mpr hden_pos
  simpa [Goldbach.AO_WeightMass.weight_mass] using sq_pos_of_pos hwScale_pos

/-- The natural raw/log-scaled statistic obtained by dividing `corr_integral` by `weight_mass(X)`. -/
noncomputable def corrIntegralDivWeight (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * corr_integral X N

/-- Deweighted `Q0`-major object. -/
noncomputable def corrIntegralMajorQ0DivWeight (X N : ℕ) (Δ : ℝ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * corr_integral_major_Q0 X N Δ

/-- Deweighted small-`β` major object. -/
noncomputable def corrIntegralMajorQ0SmallDivWeight (X N : ℕ) (Δ : ℝ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * corr_integral_major_Q0_small X N Δ

/-- Deweighted large-`β` major object. -/
noncomputable def corrIntegralMajorQ0LargeDivWeight (X N : ℕ) (Δ : ℝ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * corr_integral_major_Q0_large X N Δ

private lemma inv_weight_mass_norm {X : ℕ} :
    ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)‖
      = (Goldbach.AO_WeightMass.weight_mass X)⁻¹ := by
  calc
    ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)‖
        = ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))‖⁻¹ := by
            simpa using Complex.norm_inv (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
    _ = ‖(Goldbach.AO_WeightMass.weight_mass X : ℝ)‖⁻¹ := by
          simp
    _ = |Goldbach.AO_WeightMass.weight_mass X|⁻¹ := by rw [Real.norm_eq_abs]
    _ = (Goldbach.AO_WeightMass.weight_mass X)⁻¹ := by
          congr 1
          exact abs_of_nonneg (sq_nonneg _)

private lemma norm_sub_deweighted_le_of_weighted
    {X : ℕ} {z t : ℂ} {η : ℝ}
    (hX : BankParams.X0 ≤ X)
    (h :
      ‖z - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * t)‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * η) :
    ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * z) - t‖ ≤ η := by
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X :=
    weight_mass_pos_of_X0_le hX
  have hwne : (Goldbach.AO_WeightMass.weight_mass X : ℝ) ≠ 0 := ne_of_gt hwpos
  have hsplit :
      ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * z) - t
        =
      (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
        * (z - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * t)) := by
    have hmul :
          ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
              * (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * t))
            = t := by
      calc
        ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
            * (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * t))
            = ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
                * (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))) * t := by
                  ring
        _ = 1 * t := by
              rw [inv_mul_cancel₀]
              exact_mod_cast hwne
        _ = t := by ring
    calc
      ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * z) - t
          = ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * z)
              - ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
                  * (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * t)) := by
                    rw [hmul]
      _ = (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
            * (z - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * t)) := by
              ring
  calc
    ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * z) - t‖
        =
      ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
        * (z - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * t))‖ := by
          simpa using congrArg (fun w : ℂ => ‖w‖) hsplit
    _ = (Goldbach.AO_WeightMass.weight_mass X)⁻¹
          * ‖z - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * t)‖ := by
            rw [norm_mul, inv_weight_mass_norm]
    _ ≤ (Goldbach.AO_WeightMass.weight_mass X)⁻¹
          * (Goldbach.AO_WeightMass.weight_mass X * η) := by
            exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (le_of_lt hwpos))
    _ = η := by
          field_simp [hwne]

private lemma norm_deweighted_le_of_weighted
    {X : ℕ} {z : ℂ} {η : ℝ}
    (hX : BankParams.X0 ≤ X)
    (h : ‖z‖ ≤ Goldbach.AO_WeightMass.weight_mass X * η) :
    ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * z‖ ≤ η := by
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X :=
    weight_mass_pos_of_X0_le hX
  calc
    ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * z‖
        = (Goldbach.AO_WeightMass.weight_mass X)⁻¹ * ‖z‖ := by
            rw [norm_mul, inv_weight_mass_norm]
    _ ≤ (Goldbach.AO_WeightMass.weight_mass X)⁻¹
          * (Goldbach.AO_WeightMass.weight_mass X * η) := by
            exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (le_of_lt hwpos))
    _ = η := by
          field_simp [ne_of_gt hwpos]

lemma corrIntegralMajorQ0DivWeight_eq_small_add_large
    {X N : ℕ} {Δ : ℝ}
    (hInt :
      IntervalIntegrable
        (βIntegrand X N Δ)
        MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) :
    corrIntegralMajorQ0DivWeight X N Δ
      =
    corrIntegralMajorQ0SmallDivWeight X N Δ
      + corrIntegralMajorQ0LargeDivWeight X N Δ := by
  have hdecomp :
      corr_integral_major_Q0 X N Δ
        = corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ :=
    corr_integral_major_Q0_eq_small_add_large (X := X) (N := N) (Δ := Δ) hInt
  simp [corrIntegralMajorQ0DivWeight, corrIntegralMajorQ0SmallDivWeight,
    corrIntegralMajorQ0LargeDivWeight, hdecomp, mul_add]

/--
Deweighted small-`β` comparison theorem.

This is the exact theorem surface the next scalar estimate should target: after dividing by
`weight_mass(X)`, the small-`β` major arc is compared directly to `corrModelRaw(N)`.
-/
theorem norm_corrIntegralMajorQ0SmallDivWeight_sub_corrModelRaw_le_of_weighted
    {X N : ℕ} {Δ ηs : ℝ}
    (hX : BankParams.X0 ≤ X)
    (hs :
      ‖corr_integral_major_Q0_small X N Δ
          - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)
              * Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N)‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * ηs) :
    ‖corrIntegralMajorQ0SmallDivWeight X N Δ
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖ ≤ ηs := by
  simpa [corrIntegralMajorQ0SmallDivWeight, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    using norm_sub_deweighted_le_of_weighted (X := X) (z := corr_integral_major_Q0_small X N Δ)
      (t := Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N) (η := ηs) hX hs

/-- Deweighted large-`β` pure-error theorem. -/
theorem norm_corrIntegralMajorQ0LargeDivWeight_le_of_weighted
    {X N : ℕ} {Δ ηl : ℝ}
    (hX : BankParams.X0 ≤ X)
    (hl :
      ‖corr_integral_major_Q0_large X N Δ‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * ηl) :
    ‖corrIntegralMajorQ0LargeDivWeight X N Δ‖ ≤ ηl := by
  simpa [corrIntegralMajorQ0LargeDivWeight]
    using norm_deweighted_le_of_weighted (X := X) (z := corr_integral_major_Q0_large X N Δ)
      (η := ηl) hX hl

/--
Deweighted full `Q0`-major comparison from separate small-`β` and large-`β` bounds.

This keeps extraction and tail disposal separate:
- small `β` compares to `corrModelRaw`,
- large `β` is pure error.
-/
theorem norm_corrIntegralMajorQ0DivWeight_sub_corrModelRaw_le_of_small_large
    {X N : ℕ} {Δ ηs ηl : ℝ}
    (hInt :
      IntervalIntegrable
        (βIntegrand X N Δ)
        MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hs :
      ‖corrIntegralMajorQ0SmallDivWeight X N Δ
          - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖ ≤ ηs)
    (hl :
      ‖corrIntegralMajorQ0LargeDivWeight X N Δ‖ ≤ ηl) :
    ‖corrIntegralMajorQ0DivWeight X N Δ
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖ ≤ ηs + ηl := by
  rw [corrIntegralMajorQ0DivWeight_eq_small_add_large (X := X) (N := N) (Δ := Δ) hInt]
  calc
    ‖(corrIntegralMajorQ0SmallDivWeight X N Δ + corrIntegralMajorQ0LargeDivWeight X N Δ)
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖
      = ‖(corrIntegralMajorQ0SmallDivWeight X N Δ
            - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N)
            + corrIntegralMajorQ0LargeDivWeight X N Δ‖ := by ring_nf
    _ ≤ ‖corrIntegralMajorQ0SmallDivWeight X N Δ
            - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖
          + ‖corrIntegralMajorQ0LargeDivWeight X N Δ‖ := by
            simpa using
              norm_add_le
                (corrIntegralMajorQ0SmallDivWeight X N Δ
                  - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N)
                (corrIntegralMajorQ0LargeDivWeight X N Δ)
    _ ≤ ηs + ηl := add_le_add hs hl

/--
Weighted-to-deweighted full `Q0`-major theorem surface.

This is the exact additive raw major-gap theorem suggested by the new normalization diagnosis.
-/
theorem norm_corrIntegralMajorQ0DivWeight_sub_corrModelRaw_le_of_small_large_weighted
    {X N : ℕ} {Δ ηs ηl : ℝ}
    (hX : BankParams.X0 ≤ X)
    (hInt :
      IntervalIntegrable
        (βIntegrand X N Δ)
        MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hs :
      ‖corr_integral_major_Q0_small X N Δ
          - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)
              * Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N)‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * ηs)
    (hl :
      ‖corr_integral_major_Q0_large X N Δ‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * ηl) :
    ‖corrIntegralMajorQ0DivWeight X N Δ
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖ ≤ ηs + ηl := by
  exact norm_corrIntegralMajorQ0DivWeight_sub_corrModelRaw_le_of_small_large
    (X := X) (N := N) (Δ := Δ)
    hInt
    (norm_corrIntegralMajorQ0SmallDivWeight_sub_corrModelRaw_le_of_weighted
      (X := X) (N := N) (Δ := Δ) (ηs := ηs) hX hs)
    (norm_corrIntegralMajorQ0LargeDivWeight_le_of_weighted
      (X := X) (N := N) (Δ := Δ) (ηl := ηl) hX hl)

/-- Deweighted full `corr_integral` gap from minor plus deweighted `Q0`-major gap. -/
theorem norm_corrIntegralDivWeight_sub_corrModelRaw_le_of_minor_major
    {X N : ℕ} {Δ η₁ η₂ : ℝ}
    (hX : BankParams.X0 ≤ X)
    (hMinor :
      ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * η₁)
    (hMajor :
      ‖corrIntegralMajorQ0DivWeight X N Δ
          - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖ ≤ η₂) :
    ‖corrIntegralDivWeight X N
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖ ≤ η₁ + η₂ := by
  have hminor' :
      ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
          * (corr_integral X N - corr_integral_major_Q0 X N Δ))‖ ≤ η₁ := by
    exact norm_deweighted_le_of_weighted (X := X)
      (z := corr_integral X N - corr_integral_major_Q0 X N Δ) (η := η₁) hX hMinor
  have hsplit :
      corrIntegralDivWeight X N
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N
        =
      ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
          * (corr_integral X N - corr_integral_major_Q0 X N Δ))
        + (corrIntegralMajorQ0DivWeight X N Δ
            - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N) := by
    unfold corrIntegralDivWeight corrIntegralMajorQ0DivWeight
    ring_nf
  calc
    ‖corrIntegralDivWeight X N
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖
      = ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
            * (corr_integral X N - corr_integral_major_Q0 X N Δ))
          + (corrIntegralMajorQ0DivWeight X N Δ
              - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N)‖ := by
            simpa using congrArg (fun z : ℂ => ‖z‖) hsplit
    _ ≤ ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
            * (corr_integral X N - corr_integral_major_Q0 X N Δ))‖
          + ‖corrIntegralMajorQ0DivWeight X N Δ
              - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖ := by
            simpa using
              norm_add_le
                ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)
                  * (corr_integral X N - corr_integral_major_Q0 X N Δ))
                (corrIntegralMajorQ0DivWeight X N Δ
                  - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N)
    _ ≤ η₁ + η₂ := add_le_add hminor' hMajor

/--
Weighted final raw-gap theorem: minor plus split major on the raw/log-scaled deweighted surface.
-/
theorem norm_corrIntegralDivWeight_sub_corrModelRaw_le_of_minor_small_large_weighted
    {X N : ℕ} {Δ η₁ ηs ηl : ℝ}
    (hX : BankParams.X0 ≤ X)
    (hInt :
      IntervalIntegrable
        (βIntegrand X N Δ)
        MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hMinor :
      ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * η₁)
    (hSmall :
      ‖corr_integral_major_Q0_small X N Δ
          - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)
              * Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N)‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * ηs)
    (hLarge :
      ‖corr_integral_major_Q0_large X N Δ‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * ηl) :
    ‖corrIntegralDivWeight X N
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖ ≤ η₁ + (ηs + ηl) := by
  exact norm_corrIntegralDivWeight_sub_corrModelRaw_le_of_minor_major
    (X := X) (N := N) (Δ := Δ) (η₁ := η₁) (η₂ := ηs + ηl)
    hX
    hMinor
    (norm_corrIntegralMajorQ0DivWeight_sub_corrModelRaw_le_of_small_large_weighted
      (X := X) (N := N) (Δ := Δ) (ηs := ηs) (ηl := ηl) hX hInt hSmall hLarge)

end

end Goldbach.BankPieces.Cert.RawScaleMajorGap
