import Goldbach.BankPieces.Cert.TrueSingularSeries
import Goldbach.Cert.MajorArcModules.Normalization
import Goldbach.Cert.SigmaLowerOnWindowCanonSpec
import Goldbach.Cert.SigmaUpperOnWindowCanon
import Goldbach.ProjectedTrueMajorTermDirectProto
import Goldbach.Cert.CanonLogBounds
import Goldbach.CanonParams

namespace Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare

open Goldbach
open Goldbach.Windows
open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.Cert.MajorArcModules.Normalization

noncomputable section

/-- Window-uniform deterministic comparison factor from the normalized model to `Mtrue`. -/
noncomputable def Strue_from_RΛ_model (X : ℕ) : ℝ :=
  Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X /
    ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X)

private lemma weight_mass_nonneg (X : ℕ) : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
  simp [Goldbach.AO_WeightMass.weight_mass, sq_nonneg]

private lemma weight_mass_pos_of_X0_le {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) :
    0 < Goldbach.AO_WeightMass.weight_mass X := by
  have hlog_ge_ten : (10 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    linarith
  have hwScale_pos : 0 < Goldbach.BG_Bank.wScale X := by
    unfold Goldbach.BG_Bank.wScale
    have hden_pos : 0 < Real.log (X : ℝ) * (2 * (Goldbach.BG_Bank.H : ℝ) + 1) := by
      positivity
    exact one_div_pos.mpr hden_pos
  simpa [Goldbach.AO_WeightMass.weight_mass] using sq_pos_of_pos hwScale_pos

private lemma RΛ_model_nonneg_on_window {X N : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X)
    (hN : N ∈ EvenIn X Goldbach.Analytic.H) :
    0 ≤ Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N := by
  have hsigma_lower :=
    Goldbach.AO_SigmaPos.SigmaLowerOnWindow.sigma_even_lb_on_window (X := X) (N := N) hX hN
  have hsigma_nonneg : 0 ≤ Goldbach.AO_SigmaModel.sigma N := by
    exact le_trans (le_of_lt Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin_pos) hsigma_lower
  have hweight_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := weight_mass_nonneg X
  rw [RΛ_model_eq_sigma_mul_weight_mass]
  exact mul_nonneg hsigma_nonneg hweight_nonneg

lemma RΛ_model_le_Q0_weight_mass_on_window {X N : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X)
    (hN : N ∈ EvenIn X Goldbach.Analytic.H) :
    Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N
      ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X := by
  have hsigma_abs :=
    Goldbach.AO_SigmaPos.SigmaUpperOnWindow.sigma_even_ub_on_window (X := X) (N := N) hX hN
  have hsigma_nonneg : 0 ≤ Goldbach.AO_SigmaModel.sigma N :=
    RΛ_model_nonneg_on_window hX hN |> fun h =>
      by
        have hweight_pos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_X0_le hX
        rw [RΛ_model_eq_sigma_mul_weight_mass] at h
        exact nonneg_of_mul_nonneg_left h hweight_pos
  have hsigma_leQ0 : Goldbach.AO_SigmaModel.sigma N ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
    simpa [Goldbach.Cert.SigmaUpperOnWindowCanon.Cσ_eq_Q0, abs_of_nonneg hsigma_nonneg] using hsigma_abs
  have hweight_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := weight_mass_nonneg X
  rw [RΛ_model_eq_sigma_mul_weight_mass]
  exact mul_le_mul_of_nonneg_right hsigma_leQ0 hweight_nonneg

lemma Strue_from_RΛ_model_pos {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) :
    0 < Strue_from_RΛ_model X := by
  have hL_pos : 0 < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X := by
    have hbase_pos : 0 < ramanujanSeriesGlobal.sigma 2 := ramanujanSeriesShape.base_pos
    have hnum_pos : 0 < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < Goldbach.Analytic.X0) hX)
    have hden_pos :
        0 < (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2 := by
      have hXH_ge_X0 : Goldbach.Analytic.X0 ≤ X + Goldbach.Analytic.H := by
        exact le_trans hX (Nat.le_add_right X Goldbach.Analytic.H)
      have hlog_ge_ten : (10 : ℝ) ≤ Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) :=
        Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
      have hlog_pos : 0 < Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) := by
        linarith
      exact sq_pos_of_pos hlog_pos
    unfold Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue
    exact mul_pos hbase_pos (div_pos hnum_pos hden_pos)
  have hweight_pos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_X0_le hX
  have hQ0_pos : 0 < (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
  unfold Strue_from_RΛ_model
  exact div_pos hL_pos (mul_pos hQ0_pos hweight_pos)

/-- The true Hardy--Littlewood term dominates the normalized major-arc model after an `X`-only rescaling. -/
theorem Strue_from_RΛ_model_mul_RΛ_model_le_Mtrue {X N : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X)
    (hN : N ∈ EvenIn X Goldbach.Analytic.H) :
    Strue_from_RΛ_model X * Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N
      ≤ Goldbach.ProjectedTrueMajorTermDirectProto.Mtrue X N := by
  have hden_pos :
      0 <
        (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X := by
    have hQ0_pos : 0 < (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
      norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
    exact mul_pos hQ0_pos (weight_mass_pos_of_X0_le hX)
  have hRmodel_le :
      Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N
        ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X :=
    RΛ_model_le_Q0_weight_mass_on_window hX hN
  have hscaled :
      Strue_from_RΛ_model X * Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N
        ≤ Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X := by
    have hcoef_nonneg : 0 ≤ Strue_from_RΛ_model X := le_of_lt (Strue_from_RΛ_model_pos hX)
    have hmul :
        Strue_from_RΛ_model X
            * Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N
          ≤
        Strue_from_RΛ_model X
            * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X) := by
      exact mul_le_mul_of_nonneg_left hRmodel_le hcoef_nonneg
    have hcancel :
        Strue_from_RΛ_model X
            * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * Goldbach.AO_WeightMass.weight_mass X)
          = Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue X := by
      have hQ0_ne : (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) ≠ 0 := by
        norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
      have hweight_ne : Goldbach.AO_WeightMass.weight_mass X ≠ 0 :=
        ne_of_gt (weight_mass_pos_of_X0_le hX)
      unfold Strue_from_RΛ_model
      field_simp [hQ0_ne, hweight_ne]
    exact le_trans hmul (by rw [hcancel])
  exact le_trans hscaled (Goldbach.ProjectedTrueMajorTermDirectProto.projected_true_major_lower hX hN)

private lemma weight_mass_le_inv20001_sq {X : ℕ}
    (hX : Goldbach.BankParams.X0 ≤ X) :
    Goldbach.AO_WeightMass.weight_mass X ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    exact le_trans (by norm_num)
      (Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX)
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    linarith
  have hw :
      Goldbach.BG_Bank.wScale X ≤ (1 : ℝ) / (20001 : ℝ) := by
    have hw0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    have hw_le_mul :
        Goldbach.BG_Bank.wScale X ≤ Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) := by
      nlinarith
    have hscale :
        Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) = (1 : ℝ) / (20001 : ℝ) := by
      have hlogne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlog_pos
      have h20001r : (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1 = (20001 : ℝ) := by
        norm_num [Goldbach.BG_Bank.H, Goldbach.BankParams.H]
      unfold Goldbach.BG_Bank.wScale
      set d : ℝ := (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1
      have hd20001 : d = (20001 : ℝ) := by simpa [d] using h20001r
      calc
        (1 : ℝ) / (Real.log (X : ℝ) * (2 * Goldbach.BG_Bank.H + 1)) * Real.log (X : ℝ)
            = (1 : ℝ) / (Real.log (X : ℝ) * d) * Real.log (X : ℝ) := by
                simp [d, Nat.cast_add, Nat.cast_mul]
        _ = Real.log (X : ℝ) / (Real.log (X : ℝ) * d) := by
              simpa using
                (one_div_mul_eq_div (a := Real.log (X : ℝ) * d) (b := Real.log (X : ℝ)))
        _ = (Real.log (X : ℝ) * (1 : ℝ)) / (Real.log (X : ℝ) * d) := by
              simp [mul_assoc]
        _ = (1 : ℝ) / d := by
              simpa [mul_assoc] using
                (mul_div_mul_left (c := Real.log (X : ℝ)) (a := (1 : ℝ)) (b := d) hlogne)
        _ = (1 : ℝ) / (20001 : ℝ) := by
              simp [hd20001]
    exact le_trans hw_le_mul (by simpa [hscale])
  have hw0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
  have hcap0 : 0 ≤ (1 : ℝ) / (20001 : ℝ) := by norm_num
  have hsq :
      (Goldbach.BG_Bank.wScale X) ^ 2 ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
    have := mul_le_mul hw hw hw0 hcap0
    simpa [pow_two] using this
  simpa [Goldbach.AO_WeightMass.weight_mass] using hsq

private lemma sigma_two_ge_one :
    1 ≤ ramanujanSeriesGlobal.sigma 2 := by
  have htrunc : (33 : ℝ) / 25 ≤ Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 2 :=
    Goldbach.Cert.SigmaTruncQ0At2Cert.sigma_trunc_Q0_two_ge_33_25
  have htail_abs :
      |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail 2|
        ≤ (180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2 := by
    simpa using
      (Goldbach.Cert.SigmaTailRealBoundFun.sigmaTail_abs_le_180_div_Q_mul_N_sq
        Goldbach.AO_OffDiag.TailBlock.Q0 2 (by decide) (by simp [Goldbach.AO_OffDiag.TailBlock.Q0]))
  have htail_lower :
      -((180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2)
        ≤ Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail 2 := by
    exact (abs_le.mp htail_abs).1
  have hsigma :
      ramanujanSeriesGlobal.sigma 2
        = Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 2
            + Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail 2 := by
    simp [ramanujanSeriesGlobal,
      Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan]
  have hnum :
      1 < (33 : ℝ) / 25
        - ((180 : ℝ) / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (2 : ℝ) ^ 2) := by
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
  rw [hsigma]
  nlinarith

private lemma log_X0H_lt_fourteen :
    Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) < (14 : ℝ) := by
  have hpow : Goldbach.Analytic.X0 + Goldbach.Analytic.H ≤ (2 : ℕ) ^ 20 := by
    decide
  have hpow' : (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) ≤ (2 : ℝ) ^ 20 := by
    exact_mod_cast hpow
  have hpos : (0 : ℝ) < (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) := by
    norm_num [Goldbach.Analytic.X0, Goldbach.BankParams.X0, Goldbach.Analytic.H, Goldbach.BankParams.H]
  have hlog_le :
      Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))
        ≤ Real.log ((2 : ℝ) ^ 20) := by
    exact Real.log_le_log hpos hpow'
  have hlog2 : Real.log (2 : ℝ) < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hmul : (20 : ℝ) * Real.log (2 : ℝ) < (20 : ℝ) * (0.6931471808 : ℝ) := by
    exact mul_lt_mul_of_pos_left hlog2 (by norm_num)
  have hmul' : (20 : ℝ) * (0.6931471808 : ℝ) < (14 : ℝ) := by
    norm_num
  have hlog_pow_lt : Real.log ((2 : ℝ) ^ 20) < (14 : ℝ) := by
    simpa [Real.log_pow] using lt_trans hmul hmul'
  exact lt_of_le_of_lt hlog_le hlog_pow_lt

private lemma scale_X0_ge_5000 :
    (5000 : ℝ)
      ≤ ((Goldbach.Analytic.X0 : ℝ)
          / (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2) := by
  have hlog_sq_le :
      (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2 ≤ (14 : ℝ) ^ 2 := by
    have hlog_nonneg : 0 ≤ Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) := by
      have hXH_ge_X0 : Goldbach.Analytic.X0 ≤ Goldbach.Analytic.X0 + Goldbach.Analytic.H := by
        exact Nat.le_add_right Goldbach.Analytic.X0 Goldbach.Analytic.H
      have hlog_ge_ten :
          (10 : ℝ) ≤ Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) :=
        Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
      linarith
    have habs_le :
        |Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))| ≤ |(14 : ℝ)| := by
      have hlog_nonneg' : 0 ≤ Real.log ((Goldbach.Analytic.X0 : ℝ) + Goldbach.Analytic.H) := by
        simpa [Nat.cast_add] using hlog_nonneg
      calc
        |Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))|
            = Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) := by
                simp [Nat.cast_add, abs_of_nonneg hlog_nonneg']
        _ ≤ 14 := (log_X0H_lt_fourteen).le
        _ = |(14 : ℝ)| := by norm_num
    exact sq_le_sq.mpr habs_le
  have hlog_sq_pos :
      0 < (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2 := by
    have hXH_ge_X0 : Goldbach.Analytic.X0 ≤ Goldbach.Analytic.X0 + Goldbach.Analytic.H := by
      exact Nat.le_add_right Goldbach.Analytic.X0 Goldbach.Analytic.H
    have hlog_ge_ten :
        (10 : ℝ) ≤ Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
    have hlog_pos :
        0 < Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) := by
      linarith
    exact sq_pos_of_pos hlog_pos
  have hinv :
      ((14 : ℝ) ^ 2)⁻¹
        ≤ (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlog_sq_pos hlog_sq_le
  have hmul :
      (Goldbach.Analytic.X0 : ℝ) * (((14 : ℝ) ^ 2)⁻¹)
        ≤ (Goldbach.Analytic.X0 : ℝ)
            * ((Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)⁻¹) := by
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hnum : (5000 : ℝ) ≤ (Goldbach.Analytic.X0 : ℝ) * (((14 : ℝ) ^ 2)⁻¹) := by
    norm_num [Goldbach.Analytic.X0, Goldbach.BankParams.X0]
  calc
    (5000 : ℝ) ≤ (Goldbach.Analytic.X0 : ℝ) * (((14 : ℝ) ^ 2)⁻¹) := hnum
    _ ≤ (Goldbach.Analytic.X0 : ℝ)
          * ((Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)⁻¹) := hmul
    _ = ((Goldbach.Analytic.X0 : ℝ)
          / (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2) := by
          rw [div_eq_mul_inv]

lemma RΛ_model_at_X0_lt_Ltrue_at_X0 :
    Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model Goldbach.Analytic.X0 Goldbach.Analytic.X0
      < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
  have hEven : Goldbach.Analytic.X0 ∈ EvenIn Goldbach.Analytic.X0 Goldbach.Analytic.H := by
    exact Goldbach.Windows.mem_EvenIn_self (Goldbach.Windows.isEven_of_even (by decide : Even Goldbach.Analytic.X0))
  have hRmodel_le :
      Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model Goldbach.Analytic.X0 Goldbach.Analytic.X0
        ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
            * Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0 := by
    exact RΛ_model_le_Q0_weight_mass_on_window le_rfl hEven
  have hweight :
      Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0
        ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := weight_mass_le_inv20001_sq le_rfl
  have hRmodel_lt_one :
      Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model Goldbach.Analytic.X0 Goldbach.Analytic.X0 < 1 := by
    have hcap :
        Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model Goldbach.Analytic.X0 Goldbach.Analytic.X0
          ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
      exact le_trans hRmodel_le (mul_le_mul_of_nonneg_left hweight (by positivity))
    have hnum :
        (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) < 1 := by
      norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
    exact lt_of_le_of_lt hcap hnum
  have hLtrue_ge :
      (5000 : ℝ) ≤ Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
    have hscale : (5000 : ℝ)
        ≤ ((Goldbach.Analytic.X0 : ℝ)
            / (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2) :=
      scale_X0_ge_5000
    have hs2_nonneg : 0 ≤ ramanujanSeriesGlobal.sigma 2 := le_trans (by norm_num) sigma_two_ge_one
    have hmul := mul_le_mul_of_nonneg_right hscale hs2_nonneg
    have hfivek : (5000 : ℝ) ≤ (5000 : ℝ) * ramanujanSeriesGlobal.sigma 2 := by
      nlinarith [sigma_two_ge_one]
    simpa [Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue, mul_comm, mul_left_comm, mul_assoc]
      using le_trans hfivek hmul
  have hlt : (1 : ℝ) < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
    exact lt_of_lt_of_le (by norm_num) hLtrue_ge
  exact lt_of_lt_of_le hRmodel_lt_one hlt.le

lemma one_lt_Ltrue_at_X0 :
    (1 : ℝ) < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
  have hLtrue_ge :
      (5000 : ℝ) ≤ Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
    have hscale : (5000 : ℝ)
        ≤ ((Goldbach.Analytic.X0 : ℝ)
            / (Real.log (((Goldbach.Analytic.X0 + Goldbach.Analytic.H : ℕ) : ℝ))) ^ 2) :=
      scale_X0_ge_5000
    have hs2_nonneg : 0 ≤ ramanujanSeriesGlobal.sigma 2 := le_trans (by norm_num) sigma_two_ge_one
    have hmul := mul_le_mul_of_nonneg_right hscale hs2_nonneg
    have hfivek : (5000 : ℝ) ≤ (5000 : ℝ) * ramanujanSeriesGlobal.sigma 2 := by
      nlinarith [sigma_two_ge_one]
    simpa [Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue, mul_comm, mul_left_comm, mul_assoc]
      using le_trans hfivek hmul
  exact lt_of_lt_of_le (by norm_num) hLtrue_ge

lemma Q0_weight_mass_at_X0_lt_Ltrue_at_X0 :
    (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
        * Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0
      < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 := by
  have hweight :
      Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0
        ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := weight_mass_le_inv20001_sq le_rfl
  have hcap :
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
          * Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0
        ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hweight (by positivity)
  have hnum :
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) < 1 := by
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
  have hlt1 :
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
          * Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0 < 1 := by
    exact lt_of_le_of_lt hcap hnum
  exact lt_trans hlt1 one_lt_Ltrue_at_X0

lemma Q0_weight_mass_at_X0_lt_eps :
    (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
        * Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0
      < Goldbach.CanonParams.ε := by
  have hweight :
      Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0
        ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := weight_mass_le_inv20001_sq le_rfl
  have hcap :
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
          * Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0
        ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hweight (by positivity)
  have hnum :
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) * (((1 : ℝ) / (20001 : ℝ)) ^ 2)
        < Goldbach.CanonParams.ε := by
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0, Goldbach.CanonParams.ε]
  exact lt_of_le_of_lt hcap hnum

lemma RΛ_model_at_X0_lt_eps :
    Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model Goldbach.Analytic.X0 Goldbach.Analytic.X0
      < Goldbach.CanonParams.ε := by
  have hEven : Goldbach.Analytic.X0 ∈ EvenIn Goldbach.Analytic.X0 Goldbach.Analytic.H := by
    exact Goldbach.Windows.mem_EvenIn_self
      (Goldbach.Windows.isEven_of_even (by decide : Even Goldbach.Analytic.X0))
  have hRmodel_le :
      Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model Goldbach.Analytic.X0 Goldbach.Analytic.X0
        ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
            * Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0 := by
    exact RΛ_model_le_Q0_weight_mass_on_window le_rfl hEven
  exact lt_of_le_of_lt hRmodel_le Q0_weight_mass_at_X0_lt_eps

/-- The natural model-scale lower margin coming from the sigma lower bound. -/
noncomputable def cModel [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] (X : ℕ) : ℝ :=
  Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin * Goldbach.AO_WeightMass.weight_mass X

lemma cModel_le_RΛ_model_on_window
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    {X N : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X)
    (hN : N ∈ EvenIn X Goldbach.Analytic.H) :
    cModel X ≤ Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N := by
  have hsigma :=
    Goldbach.AO_SigmaPos.SigmaLowerOnWindow.sigma_even_lb_on_window (X := X) (N := N) hX hN
  rw [Goldbach.Cert.MajorArcModules.Normalization.RΛ_model_eq_sigma_mul_weight_mass]
  unfold cModel
  exact mul_le_mul_of_nonneg_right hsigma (weight_mass_nonneg X)

lemma cModel_at_X0_lt_eps
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] :
    cModel Goldbach.Analytic.X0 < Goldbach.CanonParams.ε := by
  have hEven : Goldbach.Analytic.X0 ∈ EvenIn Goldbach.Analytic.X0 Goldbach.Analytic.H := by
    exact Goldbach.Windows.mem_EvenIn_self
      (Goldbach.Windows.isEven_of_even (by decide : Even Goldbach.Analytic.X0))
  exact lt_of_le_of_lt
    (cModel_le_RΛ_model_on_window (X := Goldbach.Analytic.X0) (N := Goldbach.Analytic.X0) le_rfl hEven)
    RΛ_model_at_X0_lt_eps

lemma one_lt_Strue_from_RΛ_model_at_X0 :
    (1 : ℝ) < Strue_from_RΛ_model Goldbach.Analytic.X0 := by
  have hden_pos :
      0 <
        (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
          * Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0 := by
    have hQ0_pos : 0 < (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
      norm_num [Goldbach.AO_OffDiag.TailBlock.Q0]
    exact mul_pos hQ0_pos (weight_mass_pos_of_X0_le le_rfl)
  unfold Strue_from_RΛ_model
  have hlt :
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)
          * Goldbach.AO_WeightMass.weight_mass Goldbach.Analytic.X0
        < Goldbach.ProjectedTrueMajorTermDirectProto.Ltrue Goldbach.Analytic.X0 :=
    Q0_weight_mass_at_X0_lt_Ltrue_at_X0
  simpa using (one_lt_div hden_pos).2 hlt

end

end Goldbach.BankPieces.Cert.ProjectedTrueScaleCompare
