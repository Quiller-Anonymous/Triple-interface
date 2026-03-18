import Goldbach.BankPieces.Cert.RawScaleMajorGap
import Goldbach.BankPieces.Cert.ProjectedConstGapBridge
import Goldbach.Cert.MajorArcModules.CorrModel

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaModel

open Complex
open Goldbach
open Goldbach.Cert.MajorArcModules.MainTermQ0
open Goldbach.BankPieces.Cert.ProjectedConstGapBridge

noncomputable section

private lemma qaPhaseUpperConst_nonneg : 0 ≤ qaPhaseUpperConst := by
  unfold qaPhaseUpperConst
  refine Finset.sum_nonneg ?_
  intro q hq
  have hmu_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q := by
    by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]
  have hphi_nonneg : 0 ≤ (Nat.totient q : ℝ) := by positivity
  exact div_nonneg hmu_nonneg hphi_nonneg

private lemma weight_mass_pos_of_X0_le {X : ℕ} (hX : Goldbach.BankParams.X0 ≤ X) :
    0 < Goldbach.AO_WeightMass.weight_mass X := by
  have hlog_ge : (10 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    linarith
  have hden_pos : 0 < Real.log (X : ℝ) * (2 * (Goldbach.BankParams.H : ℝ) + 1) := by
    positivity
  have hwScale_pos : 0 < Goldbach.BG_Bank.wScale X := by
    dsimp [Goldbach.BG_Bank.wScale]
    exact one_div_pos.mpr hden_pos
  simpa [Goldbach.AO_WeightMass.weight_mass] using sq_pos_of_pos hwScale_pos

private lemma norm_sub_deweighted_le_of_weighted
    {X : ℕ} {z t : ℂ} {η : ℝ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (h :
      ‖z - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * t)‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * η) :
    ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹) * z) - t‖ ≤ η := by
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_X0_le hX
  have hwne : (Goldbach.AO_WeightMass.weight_mass X : ℝ) ≠ 0 := ne_of_gt hwpos
  have hinv_norm :
      ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)‖
        = (Goldbach.AO_WeightMass.weight_mass X)⁻¹ := by
    calc
      ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)⁻¹)‖
          = ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))‖⁻¹ := by
              simpa using norm_inv (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
      _ = ‖(Goldbach.AO_WeightMass.weight_mass X : ℝ)‖⁻¹ := by simp
      _ = |Goldbach.AO_WeightMass.weight_mass X|⁻¹ := by rw [Real.norm_eq_abs]
      _ = (Goldbach.AO_WeightMass.weight_mass X)⁻¹ := by
            congr 1
            exact abs_of_nonneg (sq_nonneg _)
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
            rw [norm_mul, hinv_norm]
    _ ≤ (Goldbach.AO_WeightMass.weight_mass X)⁻¹
          * (Goldbach.AO_WeightMass.weight_mass X * η) := by
            exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (le_of_lt hwpos))
    _ = η := by field_simp [hwne]

/--
Temporary raw small-`β` model with an explicit archimedean scalar `A(X,N)` multiplying the
truncated `q,a` main term.

This is the right intermediate target for the raw small-`β` theorem: extraction first, then a
separate scalar comparison to `corrModelRaw`.
-/
noncomputable def smallBetaModelRaw (A : ℕ → ℕ → ℝ) (X N : ℕ) : ℂ :=
  ((A X N : ℝ) : ℂ) * qa_mainTerm_Q0C N

/--
The same temporary small-`β` model on the original weighted/windowed `corr_integral` scale.

This is the exact extraction target before dividing out `weight_mass(X)`.
-/
noncomputable def smallBetaModelWeighted (A : ℕ → ℕ → ℝ) (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * smallBetaModelRaw A X N

/-- The target scalar occurring in `corrModelRaw`. -/
noncomputable def corrModelRawScalar (N : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even

lemma corrModelRaw_eq_smallBetaModelRaw_target (N : ℕ) :
    Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N
      = smallBetaModelRaw (fun _ N => corrModelRawScalar N) N N := by
  simp [smallBetaModelRaw, corrModelRawScalar,
    Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw_eq_logSq_mul_massEven_mul_qa_mainTerm_Q0C,
    mul_assoc, mul_left_comm, mul_comm]

lemma smallBetaModelWeighted_eq_weightMass_mul_raw (A : ℕ → ℕ → ℝ) (X N : ℕ) :
    smallBetaModelWeighted A X N
      = (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * smallBetaModelRaw A X N := by
  rfl

theorem norm_corrIntegralMajorQ0SmallDivWeight_sub_smallBetaModelRaw_le_of_weighted_extract
    (A : ℕ → ℕ → ℝ)
    {X N : ℕ} {Δ ηextract : ℝ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hextract :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
          - smallBetaModelWeighted A X N‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * ηextract) :
    ‖Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight X N Δ
        - smallBetaModelRaw A X N‖ ≤ ηextract := by
  simpa [Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight,
    smallBetaModelWeighted, smallBetaModelRaw, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    using norm_sub_deweighted_le_of_weighted
      (X := X)
      (z := Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ)
      (t := smallBetaModelRaw A X N) (η := ηextract) hX hextract

lemma norm_smallBetaModelRaw_sub_corrModelRaw_le_of_scalar_gap
    (A : ℕ → ℕ → ℝ) {X N : ℕ} {ηA : ℝ}
    (hA : |A X N - corrModelRawScalar N| ≤ ηA) :
    ‖smallBetaModelRaw A X N - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖
      ≤ ηA * qaPhaseUpperConst := by
  have hηA_nonneg : 0 ≤ ηA := by
    exact le_trans (abs_nonneg _) hA
  have hsplit :
      smallBetaModelRaw A X N - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N
        =
      (((A X N - corrModelRawScalar N : ℝ)) : ℂ) * qa_mainTerm_Q0C N := by
    rw [Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw_eq_logSq_mul_massEven_mul_qa_mainTerm_Q0C]
    simp [smallBetaModelRaw, corrModelRawScalar, sub_eq_add_neg, mul_add, add_mul,
      mul_assoc, mul_left_comm, mul_comm]
  calc
    ‖smallBetaModelRaw A X N - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖
        = ‖((((A X N - corrModelRawScalar N : ℝ)) : ℂ) * qa_mainTerm_Q0C N)‖ := by
            simpa using congrArg (fun z : ℂ => ‖z‖) hsplit
    _ = |A X N - corrModelRawScalar N| * ‖qa_mainTerm_Q0C N‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |A X N - corrModelRawScalar N| * qaPhaseUpperConst := by
          exact mul_le_mul_of_nonneg_left
            (norm_qa_mainTerm_Q0C_le_qaPhaseUpperConst (N := N))
            (abs_nonneg _)
    _ ≤ ηA * qaPhaseUpperConst := by
          exact mul_le_mul_of_nonneg_right hA qaPhaseUpperConst_nonneg

theorem norm_corrIntegralMajorQ0SmallDivWeight_sub_corrModelRaw_le_of_extract_scalar
    (A : ℕ → ℕ → ℝ)
    {X N : ℕ} {Δ ηextract ηA : ℝ}
    (hextract :
      ‖Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight X N Δ
          - smallBetaModelRaw A X N‖ ≤ ηextract)
    (hA : |A X N - corrModelRawScalar N| ≤ ηA) :
    ‖Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight X N Δ
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖
      ≤ ηextract + ηA * qaPhaseUpperConst := by
  calc
    ‖Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight X N Δ
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖
      =
    ‖(Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight X N Δ
          - smallBetaModelRaw A X N)
        + (smallBetaModelRaw A X N
            - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N)‖ := by
          ring_nf
    _ ≤ ‖Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight X N Δ
            - smallBetaModelRaw A X N‖
          + ‖smallBetaModelRaw A X N
              - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖ := by
            simpa using
              norm_add_le
                (Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight X N Δ
                  - smallBetaModelRaw A X N)
                (smallBetaModelRaw A X N
                  - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N)
    _ ≤ ηextract + ηA * qaPhaseUpperConst := by
          gcongr
          exact norm_smallBetaModelRaw_sub_corrModelRaw_le_of_scalar_gap (A := A) hA

theorem norm_corrIntegralMajorQ0SmallDivWeight_sub_corrModelRaw_le_of_weighted_extract_scalar
    (A : ℕ → ℕ → ℝ)
    {X N : ℕ} {Δ ηextract ηA : ℝ}
    (hX : Goldbach.BankParams.X0 ≤ X)
    (hextract :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
          - (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * smallBetaModelRaw A X N)‖
        ≤ Goldbach.AO_WeightMass.weight_mass X * ηextract)
    (hA : |A X N - corrModelRawScalar N| ≤ ηA) :
    ‖Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight X N Δ
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N‖
      ≤ ηextract + ηA * qaPhaseUpperConst := by
  refine norm_corrIntegralMajorQ0SmallDivWeight_sub_corrModelRaw_le_of_extract_scalar
    (A := A) ?_ hA
  have hdeweighted :
      ‖Goldbach.BankPieces.Cert.RawScaleMajorGap.corrIntegralMajorQ0SmallDivWeight X N Δ
          - smallBetaModelRaw A X N‖ ≤ ηextract := by
    exact norm_corrIntegralMajorQ0SmallDivWeight_sub_smallBetaModelRaw_le_of_weighted_extract
      (A := A) (X := X) (N := N) (Δ := Δ) (ηextract := ηextract) hX hextract
  exact hdeweighted

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaModel
