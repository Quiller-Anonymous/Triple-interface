import Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
import Goldbach.BankPieces.Cert.RawScaleMajorGap
import Goldbach.BankPieces.Cert.RawScaleSmallBetaQGap
import Goldbach.BankPieces.Cert.ProjectedConstGapBridge
import Goldbach.Cert.MajorArcModules.CorrModel
import Goldbach.Cert.MajorArcStep24AnalyticMainTerm

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaQGapC

open scoped BigOperators Interval

open Complex MeasureTheory
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
open Goldbach.Cert.MajorArcStep24AnalyticMainTerm
open Goldbach.BankPieces.Cert.ProjectedConstGapBridge

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0
private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

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

private theorem norm_qPhaseFactor_le (q N : ℕ) :
    ‖qPhaseFactor q N‖ ≤ Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
  by_cases hq0 : q = 0
  · subst q
    simp [qPhaseFactor, Goldbach.AO_OffDiag.TailBlock.muSq]
  have hmu_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q := by
    by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]
  have hphi_pos_nat : 0 < Nat.totient q := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
  have hphi_pos : 0 < (Nat.totient q : ℝ) := by exact_mod_cast hphi_pos_nat
  have hfrac_nonneg : 0 ≤ (1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) := by positivity
  calc
    ‖qPhaseFactor q N‖
        =
      Goldbach.AO_OffDiag.TailBlock.muSq q
        * (1 / ((Nat.totient q : ℝ) ^ 2))
        * ‖∑ r ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            Goldbach.Cert.MajorArcExponential.e (-((N : ℝ) * (r : ℝ) / q))‖ := by
          rw [qPhaseFactor, norm_mul, norm_mul]
          rw [Goldbach.Cert.MajorArcStep24MainTermIdentification.moebius_sq_cast_eq_muSq]
          simp [abs_of_nonneg hmu_nonneg, mul_assoc]
    _ ≤ Goldbach.AO_OffDiag.TailBlock.muSq q
          * (1 / ((Nat.totient q : ℝ) ^ 2))
          * (Nat.totient q : ℝ) := by
            exact mul_le_mul_of_nonneg_left
              (by
                calc
                  ‖∑ r ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
                      Goldbach.Cert.MajorArcExponential.e (-((N : ℝ) * (r : ℝ) / q))‖
                    = ‖star (Goldbach.Cert.MajorArcStep23RamanujanSum.ramanujanSumC q N)‖ := by
                        rw [Goldbach.Cert.MajorArcStep24MainTermIdentification.phaseSum_neg_eq_star_ramanujanSumC]
                  _ = ‖Goldbach.Cert.MajorArcStep23RamanujanSum.ramanujanSumC q N‖ := by simp
                  _ ≤ (Nat.totient q : ℝ) := by
                        exact Goldbach.Cert.MajorArcStep23RamanujanSum.norm_ramanujanSumC_le_totient q N)
              (mul_nonneg hmu_nonneg hfrac_nonneg)
    _ = Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
          field_simp [show (Nat.totient q : ℝ) ≠ 0 by positivity]

/-- Common complex scalar model after collapsing the `q`-level family. -/
noncomputable def smallBetaModelRawC (A : ℕ → ℕ → ℂ) (X N : ℕ) : ℂ :=
  A X N * qa_mainTerm_Q0C N

/-- Weighted version of the common complex small-`β` model. -/
noncomputable def smallBetaModelWeightedC (A : ℕ → ℕ → ℂ) (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * smallBetaModelRawC A X N

theorem smallBetaModelWeightedQC_eq_smallBetaModelWeightedC
    (Aq : ℕ → ℕ → ℕ → ℂ) (A : ℕ → ℕ → ℂ)
    {X N : ℕ}
    (hAq :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, Aq X N q = A X N) :
    smallBetaModelWeightedQC Aq X N = smallBetaModelWeightedC A X N := by
  rw [smallBetaModelWeightedQC, smallBetaModelWeightedC, smallBetaModelRawC]
  congr 1
  calc
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0, Aq X N q * qPhaseFactor q N
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0, A X N * qPhaseFactor q N := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        simp [hAq q hq]
    _ = A X N * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, qPhaseFactor q N := by
          rw [Finset.mul_sum]
    _ = A X N * qa_mainTerm_Q0C N := by
          simp [qa_mainTerm_Q0C, qPhaseFactor]

theorem norm_smallBetaModelWeightedQC_sub_smallBetaModelWeightedC_le_of_uniform_scalar_gap
    (Aq : ℕ → ℕ → ℕ → ℂ) (A : ℕ → ℕ → ℂ)
    {X N : ℕ} {ηA : ℝ}
    (hAq :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        ‖Aq X N q - A X N‖ ≤ ηA) :
    ‖smallBetaModelWeightedQC Aq X N - smallBetaModelWeightedC A X N‖
      ≤ Goldbach.AO_WeightMass.weight_mass X * (ηA * qaPhaseUpperConst) := by
  have hηA_nonneg : 0 ≤ ηA := by
    have h1 : 1 ∈ Finset.Icc (1 : ℕ) Q0 := by simp [Q0, Goldbach.AO_OffDiag.TailBlock.Q0]
    exact le_trans (norm_nonneg _) (hAq 1 h1)
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
  have hconst :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, (fun X N _q => A X N) X N q = A X N := by
        intro q hq
        rfl
  have hconstEq :
      smallBetaModelWeightedC A X N
        =
      smallBetaModelWeightedQC (fun X N _q => A X N) X N := by
        symm
        exact smallBetaModelWeightedQC_eq_smallBetaModelWeightedC
          (Aq := fun X N _q => A X N) (A := A) (X := X) (N := N) hconst
  calc
    ‖smallBetaModelWeightedQC Aq X N - smallBetaModelWeightedC A X N‖
      = ‖smallBetaModelWeightedQC Aq X N - smallBetaModelWeightedQC (fun X N _q => A X N) X N‖ := by
          rw [hconstEq]
    _ =
    ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
        * (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
            (Aq X N q - A X N) * qPhaseFactor q N)‖ := by
          let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
          have hsplit :
              smallBetaModelWeightedQC Aq X N
                - smallBetaModelWeightedQC (fun X N _q => A X N) X N
                =
              w * (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
                    (Aq X N q - A X N) * qPhaseFactor q N) := by
            unfold smallBetaModelWeightedQC
            calc
              w * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, Aq X N q * qPhaseFactor q N)
                  - w * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, A X N * qPhaseFactor q N)
                =
              w * ((∑ q ∈ Finset.Icc (1 : ℕ) Q0, Aq X N q * qPhaseFactor q N)
                    - (∑ q ∈ Finset.Icc (1 : ℕ) Q0, A X N * qPhaseFactor q N)) := by
                      ring
              _ =
              w * ((∑ x ∈ Finset.Icc (1 : ℕ) Q0, Aq X N x * qPhaseFactor x N)
                    - (∑ x ∈ Finset.Icc (1 : ℕ) Q0, A X N * qPhaseFactor x N)) := by
                      rfl
              _ =
              w * (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
                    (Aq X N q - A X N) * qPhaseFactor q N) := by
                      refine congrArg (fun z : ℂ => w * z) ?_
                      rw [← Finset.sum_sub_distrib]
                      refine Finset.sum_congr rfl ?_
                      intro q hq
                      ring
          simpa [w] using congrArg norm hsplit
    _ = Goldbach.AO_WeightMass.weight_mass X
          * ‖∑ q ∈ Finset.Icc (1 : ℕ) Q0, (Aq X N q - A X N) * qPhaseFactor q N‖ := by
            rw [norm_mul]
            simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Goldbach.AO_WeightMass.weight_mass X
          * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ‖(Aq X N q - A X N) * qPhaseFactor q N‖ := by
            gcongr
            exact norm_sum_le _ _
    _ ≤ Goldbach.AO_WeightMass.weight_mass X
          * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
              ηA * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
            gcongr with q hq
            calc
              ‖(Aq X N q - A X N) * qPhaseFactor q N‖
                  = ‖Aq X N q - A X N‖ * ‖qPhaseFactor q N‖ := by
                      rw [norm_mul]
              _ ≤ ‖Aq X N q - A X N‖
                    * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
                      exact mul_le_mul_of_nonneg_left
                        (norm_qPhaseFactor_le q N)
                        (norm_nonneg _)
              _ ≤ ηA * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
                      have hterm_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
                        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
                        have hphi_pos : 0 < (Nat.totient q : ℝ) := by
                          exact_mod_cast Nat.totient_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq1)
                        exact div_nonneg
                          (by
                            by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq])
                          (le_of_lt hphi_pos)
                      exact mul_le_mul_of_nonneg_right
                        (hAq q hq)
                        hterm_nonneg
    _ = Goldbach.AO_WeightMass.weight_mass X * (ηA * qaPhaseUpperConst) := by
          rw [← Finset.mul_sum]
          simp [qaPhaseUpperConst, mul_assoc, mul_left_comm, mul_comm]

theorem norm_corr_integral_major_Q0_small_sub_smallBetaModelWeightedC_le_of_AqLocalC_residual_collapse
    (A : ℕ → ℕ → ℂ)
    {X N : ℕ} {ηres ηA : ℝ}
    (hX : 2 ≤ X)
    (hsep : Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X (1 : ℝ))
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a (1 : ℝ)).indicator
                    (fun α =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
          volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hres : ‖smallBetaResidualWeighted X N (1 : ℝ)‖ ≤ ηres)
    (hcollapse :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ‖AqLocalC X N q - A X N‖ ≤ ηA) :
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - smallBetaModelWeightedC A X N‖
      ≤ ηres + Goldbach.AO_WeightMass.weight_mass X * (ηA * qaPhaseUpperConst) := by
  have hextract :
      ‖smallBetaExtractedWeighted X N (1 : ℝ) - smallBetaModelWeightedQC AqLocalC X N‖ ≤ 0 := by
    rw [smallBetaExtractedWeighted_eq_smallBetaModelWeightedQC_AqLocalC (X := X) (N := N) hX]
    simp
  have hmain :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
          - smallBetaModelWeightedQC AqLocalC X N‖
        ≤ ηres := by
    rw [corr_integral_major_Q0_small_eq_extracted_add_residual
      (X := X) (N := N) (Δ := (1 : ℝ)) hsep hInner hOuter]
    calc
      ‖(smallBetaExtractedWeighted X N (1 : ℝ) + smallBetaResidualWeighted X N (1 : ℝ))
          - smallBetaModelWeightedQC AqLocalC X N‖
        =
      ‖(smallBetaExtractedWeighted X N (1 : ℝ) - smallBetaModelWeightedQC AqLocalC X N)
          + smallBetaResidualWeighted X N (1 : ℝ)‖ := by
            ring_nf
      _ ≤ ‖smallBetaExtractedWeighted X N (1 : ℝ) - smallBetaModelWeightedQC AqLocalC X N‖
            + ‖smallBetaResidualWeighted X N (1 : ℝ)‖ := by
              simpa using
                norm_add_le
                  (smallBetaExtractedWeighted X N (1 : ℝ) - smallBetaModelWeightedQC AqLocalC X N)
                  (smallBetaResidualWeighted X N (1 : ℝ))
      _ ≤ 0 + ηres := by
              exact add_le_add hextract hres
      _ = ηres := by ring
  calc
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - smallBetaModelWeightedC A X N‖
      ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
            - smallBetaModelWeightedQC AqLocalC X N‖
          + ‖smallBetaModelWeightedQC AqLocalC X N - smallBetaModelWeightedC A X N‖ := by
            calc
              ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                  - smallBetaModelWeightedC A X N‖
                =
              ‖(Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                    - smallBetaModelWeightedQC AqLocalC X N)
                  + (smallBetaModelWeightedQC AqLocalC X N
                    - smallBetaModelWeightedC A X N)‖ := by
                    ring_nf
              _ ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                      - smallBetaModelWeightedQC AqLocalC X N‖
                    + ‖smallBetaModelWeightedQC AqLocalC X N - smallBetaModelWeightedC A X N‖ := by
                        simpa using
                          norm_add_le
                            (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                              - smallBetaModelWeightedQC AqLocalC X N)
                            (smallBetaModelWeightedQC AqLocalC X N
                              - smallBetaModelWeightedC A X N)
    _ ≤ ηres + Goldbach.AO_WeightMass.weight_mass X * (ηA * qaPhaseUpperConst) := by
          exact add_le_add hmain
            (norm_smallBetaModelWeightedQC_sub_smallBetaModelWeightedC_le_of_uniform_scalar_gap
              (Aq := AqLocalC) (A := A) hcollapse)

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaQGapC
