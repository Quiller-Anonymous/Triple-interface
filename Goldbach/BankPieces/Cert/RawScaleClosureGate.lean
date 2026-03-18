import Goldbach.AO_SigmaPos
import Goldbach.AnalyticGlobalScaleNormEps
import Goldbach.AnalyticPointwiseScaleNormEps
import Goldbach.Cert.CanonLogBounds
import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.Cert.MajorArcModules.CorrModel
import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.RawScaleClosureGate

open Complex
open Goldbach
open Goldbach.Windows
open Goldbach.Cert.MajorArcAxiomsFunX
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.IntegralPipeline

noncomputable section

private lemma X_le_of_mem_IccShift {X H N : ℕ} (hN : N ∈ Goldbach.Windows.IccShift X H) : X ≤ N := by
  classical
  rcases Finset.mem_image.mp hN with ⟨k, hk, rfl⟩
  exact Nat.le_add_right X k

private lemma N_le_X_add_H_of_mem_IccShift {X H N : ℕ} (hN : N ∈ Goldbach.Windows.IccShift X H) :
    N ≤ X + H := by
  classical
  rcases Finset.mem_image.mp hN with ⟨k, hk, rfl⟩
  exact Nat.add_le_add_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) X

private lemma X0_le_of_mem_EvenIn {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    BankParams.X0 ≤ N := by
  have hI : N ∈ Goldbach.Windows.IccShift X BankParams.H := (Finset.mem_filter.mp hN).1
  exact le_trans hX (X_le_of_mem_IccShift (X := X) (H := BankParams.H) hI)

lemma weight_mass_pos_of_X0_le {X : ℕ} (hX : BankParams.X0 ≤ X) :
    0 < Goldbach.AO_WeightMass.weight_mass X := by
  have hlog_ge : (10 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
  have hlog_pos : 0 < Real.log (X : ℝ) := by linarith
  have hden_pos : 0 < Real.log (X : ℝ) * (2 * (BankParams.H : ℝ) + 1) := by
    positivity
  have hwScale_pos : 0 < Goldbach.BG_Bank.wScale X := by
    dsimp [Goldbach.BG_Bank.wScale]
    exact one_div_pos.mpr hden_pos
  simpa [Goldbach.AO_WeightMass.weight_mass] using sq_pos_of_pos hwScale_pos

/-- The fixed positive normalization factor relating `corr_integral` to `RΛ_smooth`. -/
private noncomputable def normFactor (N : ℕ) : ℝ :=
  (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)

/-- Window-uniform lower bound for `weight_mass(X) * normFactor(N)` on `N ∈ [X, X+H]`. -/
noncomputable def rawScaleLower (X : ℕ) : ℝ :=
  Goldbach.AO_WeightMass.weight_mass X
    * ((1 / 800 : ℝ) * (1 / (Real.log ((X + BankParams.H : ℕ) : ℝ)) ^ 2))

/-- Raw log-scaled correlation model as a real number. -/
noncomputable def corrModelRawR (N : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaModel.sigma N

/-- Canonical raw lower margin coming from the σ-lower input. -/
noncomputable def c0Raw [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] (X : ℕ) : ℝ :=
  (Real.log (X : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin

lemma corrModelRaw_eq_ofReal (N : ℕ) :
    corrModelRaw N = ((corrModelRawR N : ℝ) : ℂ) := by
  simp [corrModelRaw, corrModelRawR, mul_assoc, mul_comm]

lemma rawScaleLower_pos {X : ℕ} (hX : BankParams.X0 ≤ X) : 0 < rawScaleLower X := by
  have hweight_pos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_X0_le hX
  have hXH_ge_X0 : BankParams.X0 ≤ X + BankParams.H := by
    exact le_trans hX (Nat.le_add_right X BankParams.H)
  have hlog_ge : (10 : ℝ) ≤ Real.log ((X + BankParams.H : ℕ) : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
  have hlog_pos : 0 < Real.log ((X + BankParams.H : ℕ) : ℝ) := by
    linarith
  have hnorm_pos : 0 < (1 / 800 : ℝ) * (1 / (Real.log ((X + BankParams.H : ℕ) : ℝ)) ^ 2) := by
    have hsq_pos : 0 < (Real.log ((X + BankParams.H : ℕ) : ℝ)) ^ 2 := sq_pos_of_pos hlog_pos
    exact mul_pos (by norm_num) (one_div_pos.mpr hsq_pos)
  exact mul_pos hweight_pos hnorm_pos

lemma c0Raw_pos [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] {X : ℕ} (hX : BankParams.X0 ≤ X) :
    0 < c0Raw X := by
  have hlog_ge : (10 : ℝ) ≤ Real.log (X : ℝ) := Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
  have hlog_pos : 0 < Real.log (X : ℝ) := by linarith
  have hsq_pos : 0 < (Real.log (X : ℝ)) ^ 2 := sq_pos_of_pos hlog_pos
  have hσ_pos : 0 < Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin :=
    Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin_pos
  dsimp [c0Raw]
  positivity

lemma c0Raw_le_corrModelRawR_on_window
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    c0Raw X ≤ corrModelRawR N := by
  have hN0 : BankParams.X0 ≤ N := X0_le_of_mem_EvenIn (X := X) (N := N) hX hN
  have hX_le_N : X ≤ N := by
    have hI : N ∈ Goldbach.Windows.IccShift X BankParams.H := (Finset.mem_filter.mp hN).1
    exact X_le_of_mem_IccShift (X := X) (H := BankParams.H) hI
  have hσ :
      Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin ≤ Goldbach.AO_SigmaModel.sigma N :=
    Goldbach.AO_SigmaPos.SigmaLowerOnWindow.sigma_even_lb_on_window hX hN
  have hlog_le : Real.log (X : ℝ) ≤ Real.log (N : ℝ) := by
    have hX_pos : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < BankParams.X0) hX)
    have hX_le_NR : (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hX_le_N
    exact Real.log_le_log hX_pos hX_le_NR
  have hlogX_nonneg : 0 ≤ Real.log (X : ℝ) := by
    have hlog_ge : (10 : ℝ) ≤ Real.log (X : ℝ) := Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
    linarith
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hlog_ge : (10 : ℝ) ≤ Real.log (N : ℝ) := Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hN0
    linarith
  have hsq :
      (Real.log (X : ℝ)) ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 := by
    have hmul :=
      mul_le_mul hlog_le hlog_le hlogX_nonneg hlogN_nonneg
    simpa [pow_two] using hmul
  calc
    c0Raw X
        = (Real.log (X : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin := by
            simp [c0Raw, mul_assoc, mul_comm]
    _ ≤ (Real.log (N : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin := by
          have hsq800 :
              (Real.log (X : ℝ)) ^ 2 * (800 : ℝ)
                ≤ (Real.log (N : ℝ)) ^ 2 * (800 : ℝ) := by
            exact mul_le_mul_of_nonneg_right hsq (show 0 ≤ (800 : ℝ) by positivity)
          exact mul_le_mul_of_nonneg_right hsq800
            (le_of_lt Goldbach.AO_SigmaPos.SigmaLowerOnWindow.σmin_pos)
    _ ≤ (Real.log (N : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaModel.sigma N := by
          have hfac_nonneg : 0 ≤ (Real.log (N : ℝ)) ^ 2 * (800 : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hσ hfac_nonneg
    _ = corrModelRawR N := by
          simp [corrModelRawR, mul_assoc, mul_comm]

lemma rawScaleLower_le_weight_mass_mul_normFactor_on_window
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    rawScaleLower X ≤ Goldbach.AO_WeightMass.weight_mass X * normFactor N := by
  have hI : N ∈ Goldbach.Windows.IccShift X BankParams.H := (Finset.mem_filter.mp hN).1
  have hN_le_XH : N ≤ X + BankParams.H :=
    N_le_X_add_H_of_mem_IccShift (X := X) (H := BankParams.H) hI
  have hN0 : BankParams.X0 ≤ N := X0_le_of_mem_EvenIn (X := X) (N := N) hX hN
  have hXH_ge_X0 : BankParams.X0 ≤ X + BankParams.H := by
    exact le_trans hX (Nat.le_add_right X BankParams.H)
  have hlogN_pos : 0 < Real.log (N : ℝ) := by
    have hlog_ge : (10 : ℝ) ≤ Real.log (N : ℝ) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hN0
    linarith
  have hlogXH_pos : 0 < Real.log ((X + BankParams.H : ℕ) : ℝ) := by
    have hlog_ge : (10 : ℝ) ≤ Real.log ((X + BankParams.H : ℕ) : ℝ) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
    linarith
  have hlog_le : Real.log (N : ℝ) ≤ Real.log ((X + BankParams.H : ℕ) : ℝ) := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < BankParams.X0) hN0)
    have hcast : (N : ℝ) ≤ ((X + BankParams.H : ℕ) : ℝ) := by
      exact_mod_cast hN_le_XH
    exact Real.log_le_log hN_pos hcast
  have hsq :
      (Real.log (N : ℝ)) ^ 2 ≤ (Real.log ((X + BankParams.H : ℕ) : ℝ)) ^ 2 := by
    have hmul := mul_le_mul hlog_le hlog_le (le_of_lt hlogN_pos) (le_of_lt hlogXH_pos)
    simpa [pow_two] using hmul
  have hinv :
      (1 / (Real.log ((X + BankParams.H : ℕ) : ℝ)) ^ 2 : ℝ)
        ≤ (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) := by
    exact one_div_le_one_div_of_le (sq_pos_of_pos hlogN_pos) hsq
  have hcore :
      ((1 / 800 : ℝ) * (1 / (Real.log ((X + BankParams.H : ℕ) : ℝ)) ^ 2))
        ≤ normFactor N := by
    simpa [normFactor] using mul_le_mul_of_nonneg_left hinv (by norm_num : 0 ≤ (1 / 800 : ℝ))
  exact mul_le_mul_of_nonneg_left hcore (le_of_lt (weight_mass_pos_of_X0_le hX))

/--
Raw-scale lower bound for `conv_ref`, assuming the dewindowed major-arc gap is `η(X)` on the
canonical window.

The hypothesis is expressed without dividing by `weight_mass(X)`:
the analytic `corr_integral` is allowed to differ from `weight_mass(X) * corrModelRaw(N)` by at
most `weight_mass(X) * η(X)`.
-/
theorem raw_conv_ref_lower_of_corrModelRaw_gap
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    (η : ℕ → ℝ)
    (hη_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X → η X < c0Raw X)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N
            - ((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * corrModelRaw N‖
          ≤ Goldbach.AO_WeightMass.weight_mass X * η X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      rawScaleLower X * (c0Raw X - η X) ≤ Goldbach.BG_Identity.conv_ref X N := by
  intro X N hX hN
  have hN0 : BankParams.X0 ≤ N := X0_le_of_mem_EvenIn (X := X) (N := N) hX hN
  have hrefC :
      (Goldbach.BG_Identity.conv_ref X N : ℂ) = (normFactor N : ℂ) * corr_integral X N := by
    rw [Goldbach.Cert.MajorArcAxiomsFunX.conv_ref_eq_RΛ_smooth]
    simpa [normFactor, mul_assoc, mul_left_comm, mul_comm] using
      (RΛ_smooth_cast_eq_norm_mul_corr_integral (X := X) (N := N))
  have htargetC :
      (((normFactor N
          * Goldbach.AO_WeightMass.weight_mass X
          * corrModelRawR N : ℝ)) : ℂ)
        =
      (normFactor N : ℂ)
        * ((((Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ) * corrModelRaw N) := by
    simp [corrModelRaw_eq_ofReal, corrModelRawR, normFactor, mul_assoc, mul_left_comm, mul_comm]
  have hsplit :
      (Goldbach.BG_Identity.conv_ref X N : ℂ)
        - (((normFactor N
            * Goldbach.AO_WeightMass.weight_mass X
            * corrModelRawR N : ℝ)) : ℂ)
      =
      (normFactor N : ℂ)
        * (corr_integral X N
            - ((((Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ) * corrModelRaw N)) := by
    rw [hrefC, htargetC]
    ring
  have hnf_nonneg : 0 ≤ normFactor N := by
    have hsq_nonneg : 0 ≤ (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) :=
      one_div_nonneg.mpr (sq_nonneg _)
    simpa [normFactor] using mul_nonneg (by norm_num : 0 ≤ (1 / 800 : ℝ)) hsq_nonneg
  have hnorm :
      ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
          - (((normFactor N
                * Goldbach.AO_WeightMass.weight_mass X
                * corrModelRawR N : ℝ)) : ℂ)‖
        ≤ normFactor N * (Goldbach.AO_WeightMass.weight_mass X * η X) := by
    calc
      ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
          - (((normFactor N
                * Goldbach.AO_WeightMass.weight_mass X
                * corrModelRawR N : ℝ)) : ℂ)‖
          =
        ‖(normFactor N : ℂ)
            * (corr_integral X N
                - ((((Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ) * corrModelRaw N))‖ := by
              simpa using congrArg (fun z : ℂ => ‖z‖) hsplit
      _ = normFactor N
            * ‖corr_integral X N
                - ((((Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ) * corrModelRaw N)‖ := by
            rw [norm_mul]
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnf_nonneg]
      _ ≤ normFactor N * (Goldbach.AO_WeightMass.weight_mass X * η X) := by
            exact mul_le_mul_of_nonneg_left (hCorr hX hN) hnf_nonneg
  have hreal_abs :
      |Goldbach.BG_Identity.conv_ref X N
          - (normFactor N
              * Goldbach.AO_WeightMass.weight_mass X
              * corrModelRawR N)|
        ≤ normFactor N * (Goldbach.AO_WeightMass.weight_mass X * η X) := by
    have habs :
        |Goldbach.BG_Identity.conv_ref X N
            - (normFactor N
                * Goldbach.AO_WeightMass.weight_mass X
                * corrModelRawR N)|
          =
        ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
            - (((normFactor N
                  * Goldbach.AO_WeightMass.weight_mass X
                  * corrModelRawR N : ℝ)) : ℂ)‖ := by
      let x : ℝ :=
        Goldbach.BG_Identity.conv_ref X N
          - (normFactor N * Goldbach.AO_WeightMass.weight_mass X * corrModelRawR N)
      have hx :
          (x : ℂ)
            =
          (Goldbach.BG_Identity.conv_ref X N : ℂ)
            - (((normFactor N
                  * Goldbach.AO_WeightMass.weight_mass X
                  * corrModelRawR N : ℝ)) : ℂ) := by
        simp [x]
      calc
        |Goldbach.BG_Identity.conv_ref X N
            - (normFactor N
                * Goldbach.AO_WeightMass.weight_mass X
                * corrModelRawR N)| = |x| := by simp [x]
        _ = ‖x‖ := (Real.norm_eq_abs x).symm
        _ = ‖(x : ℂ)‖ := by simpa using (Complex.norm_real x).symm
        _ = ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
              - (((normFactor N
                    * Goldbach.AO_WeightMass.weight_mass X
                    * corrModelRawR N : ℝ)) : ℂ)‖ := by
              simpa [hx]
    rw [habs]
    exact hnorm
  have hconv_ge :
      normFactor N
          * (Goldbach.AO_WeightMass.weight_mass X * (corrModelRawR N - η X))
        ≤ Goldbach.BG_Identity.conv_ref X N := by
    have hleft := (abs_le.mp hreal_abs).1
    linarith
  have hmargin_pos : 0 < c0Raw X - η X := sub_pos.mpr (hη_lt hX)
  have hmargin_nonneg : 0 ≤ c0Raw X - η X := le_of_lt hmargin_pos
  have hmodel_ge : c0Raw X ≤ corrModelRawR N := c0Raw_le_corrModelRawR_on_window hX hN
  have hmodel_margin_ge : c0Raw X - η X ≤ corrModelRawR N - η X := sub_le_sub_right hmodel_ge _
  have hscale_ge :
      rawScaleLower X ≤ normFactor N * Goldbach.AO_WeightMass.weight_mass X := by
    simpa [mul_comm] using
      rawScaleLower_le_weight_mass_mul_normFactor_on_window (X := X) (N := N) hX hN
  have hfactor_nonneg : 0 ≤ normFactor N * Goldbach.AO_WeightMass.weight_mass X := by
    exact mul_nonneg hnf_nonneg (le_of_lt (weight_mass_pos_of_X0_le hX))
  have hprod_le :
      rawScaleLower X * (c0Raw X - η X)
        ≤ normFactor N
            * (Goldbach.AO_WeightMass.weight_mass X * (corrModelRawR N - η X)) := by
    have h1 :
        rawScaleLower X * (c0Raw X - η X)
          ≤ (normFactor N * Goldbach.AO_WeightMass.weight_mass X) * (c0Raw X - η X) := by
      exact mul_le_mul_of_nonneg_right hscale_ge hmargin_nonneg
    have h2 :
        (normFactor N * Goldbach.AO_WeightMass.weight_mass X) * (c0Raw X - η X)
          ≤ (normFactor N * Goldbach.AO_WeightMass.weight_mass X) * (corrModelRawR N - η X) := by
      exact mul_le_mul_of_nonneg_left hmodel_margin_ge hfactor_nonneg
    exact le_trans h1 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h2)
  exact le_trans hprod_le hconv_ge

/--
Raw-scale lower bound for `R_bank`, assuming a raw major-arc gap and a bank-to-reference bridge
budget measured on the same raw scale.
-/
theorem raw_R_bank_lower_of_corrModelRaw_gap
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    (η εb : ℕ → ℝ)
    (hη_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X → η X < c0Raw X)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N
            - ((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * corrModelRaw N‖
          ≤ Goldbach.AO_WeightMass.weight_mass X * η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ rawScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      rawScaleLower X * (c0Raw X - (η X + εb X)) ≤ Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  have href :
      rawScaleLower X * (c0Raw X - η X) ≤ Goldbach.BG_Identity.conv_ref X N :=
    raw_conv_ref_lower_of_corrModelRaw_gap (η := η) (hη_lt := hη_lt) (hCorr := hCorr) hX hN
  have hbridge_lower :
      Goldbach.BG_Identity.conv_ref X N - rawScaleLower X * εb X ≤ Goldbach.BG_Identity.R_bank X N := by
    have h := (abs_le.mp (hBridge hX hN)).1
    linarith
  have hsplit :
      rawScaleLower X * (c0Raw X - (η X + εb X))
        = rawScaleLower X * (c0Raw X - η X) - rawScaleLower X * εb X := by
    ring
  rw [hsplit]
  linarith

/-- Positivity consequence of the raw-scale closure gate. -/
theorem R_bank_pos_of_raw_gap
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    (η εb : ℕ → ℝ)
    (hεb_nonneg :
      ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hη_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X → η X + εb X < c0Raw X)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N
            - ((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * corrModelRaw N‖
          ≤ Goldbach.AO_WeightMass.weight_mass X * η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ rawScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  have hraw_pos : 0 < rawScaleLower X := rawScaleLower_pos hX
  have hmargin_pos : 0 < c0Raw X - (η X + εb X) := sub_pos.mpr (hη_lt hX)
  have hlower :
      rawScaleLower X * (c0Raw X - (η X + εb X)) ≤ Goldbach.BG_Identity.R_bank X N :=
    raw_R_bank_lower_of_corrModelRaw_gap
      (η := η) (εb := εb)
      (hη_lt := by
        intro X hX
        have hεb : 0 ≤ εb X := hεb_nonneg hX
        linarith [hη_lt hX])
      (hCorr := hCorr) (hBridge := hBridge) hX hN
  exact lt_of_lt_of_le (mul_pos hraw_pos hmargin_pos) hlower

/--
Variable-scale, variable-slack analytic hypothesis on the raw/log-scaled closure surface.

This is the first reusable wrapper for the raw route:
- `S(X) = rawScaleLower(X)` is the deterministic normalization from the raw scale back to `R_bank`;
- `c0(X) = c0Raw(X)` is the raw lower margin from the σ-model;
- `eps(X) = η(X) + εb(X)` is the combined raw major-arc and raw bridge budget.
-/
def analyticHypScaleNormEps_raw
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    (η εb : ℕ → ℝ)
    (hεb_nonneg :
      ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X → η X + εb X < c0Raw X)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N
            - ((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * corrModelRaw N‖
          ≤ Goldbach.AO_WeightMass.weight_mass X * η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ rawScaleLower X * εb X) :
    Goldbach.AnalyticHypScaleNormEps
      BankParams.X0
      (fun _ => BankParams.H)
      rawScaleLower
      c0Raw
      (fun X => η X + εb X) := by
  refine Goldbach.AnalyticHypScaleNormEps.ofTenor ?_
  refine Goldbach.TenorHypScaleNormEps.mkPack
    BankParams.X0
    (fun _ => BankParams.H)
    rawScaleLower
    c0Raw
    (fun X => η X + εb X)
    ?_ ?_ ?_
    (fun X _ => rawScaleLower X * c0Raw X)
    ?_ ?_
  · intro X hX
    exact rawScaleLower_pos hX
  · intro X hX
    exact c0Raw_pos hX
  · intro X hX
    exact hsum_lt hX
  · intro X N hX hN
    simp [mul_comm]
  · intro X N hX hN
    have hraw :
        rawScaleLower X * (c0Raw X - (η X + εb X)) ≤ Goldbach.BG_Identity.R_bank X N :=
      raw_R_bank_lower_of_corrModelRaw_gap
      (η := η) (εb := εb)
      (hη_lt := by
        intro X hX
        have hεb : 0 ≤ εb X := hεb_nonneg hX
        linarith [hsum_lt hX])
      (hCorr := hCorr)
      (hBridge := hBridge)
      hX hN
    have hbank :
        rawScaleLower X * c0Raw X
          - (η X + εb X) * rawScaleLower X
          ≤ Goldbach.BG_Identity.R_bank X N := by
      calc
        rawScaleLower X * c0Raw X - (η X + εb X) * rawScaleLower X
            = rawScaleLower X * (c0Raw X - (η X + εb X)) := by ring
        _ ≤ Goldbach.BG_Identity.R_bank X N := hraw
    simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using hbank

/-- Packaged pointwise witness for the raw/log-scaled closure route. -/
noncomputable def witness_rawScaleNormEps
    [Goldbach.AO_SigmaPos.SigmaLowerOnWindow]
    (η εb : ℕ → ℝ)
    (hεb_nonneg :
      ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X → η X + εb X < c0Raw X)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N
            - ((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * corrModelRaw N‖
          ≤ Goldbach.AO_WeightMass.weight_mass X * η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ rawScaleLower X * εb X) :
    Goldbach.Analytic.PointwiseWitnessScaleNormEps :=
  Goldbach.Analytic.PointwiseWitnessScaleNormEps.ofAnalytic
    (analyticHypScaleNormEps_raw
      (η := η) (εb := εb)
      (hεb_nonneg := hεb_nonneg)
      (hsum_lt := hsum_lt)
      (hCorr := hCorr)
      (hBridge := hBridge))

end

end Goldbach.BankPieces.Cert.RawScaleClosureGate
