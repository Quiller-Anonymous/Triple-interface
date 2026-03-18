import Goldbach.AnalyticGlobalScaleNormEps
import Goldbach.AnalyticPointwiseScaleNormEps
import Goldbach.Cert.CanonLogBounds
import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.IntegralScaleClosureGate

open Complex
open Goldbach
open Goldbach.Windows
open Goldbach.Cert.MajorArcAxiomsFunX
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

/-- The fixed positive normalization factor relating `corr_integral` to `conv_ref`. -/
private noncomputable def normFactor (N : ℕ) : ℝ :=
  (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)

/-- Window-uniform lower envelope for the `conv_ref` normalization factor. -/
noncomputable def convScaleLower (X : ℕ) : ℝ :=
  (1 / 800 : ℝ) * (1 / (Real.log ((X + BankParams.H : ℕ) : ℝ)) ^ 2)

lemma convScaleLower_pos {X : ℕ} (hX : BankParams.X0 ≤ X) : 0 < convScaleLower X := by
  have hXH_ge_X0 : BankParams.X0 ≤ X + BankParams.H := by
    exact le_trans hX (Nat.le_add_right X BankParams.H)
  have hlog_ge : (10 : ℝ) ≤ Real.log ((X + BankParams.H : ℕ) : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
  have hlog_pos : 0 < Real.log ((X + BankParams.H : ℕ) : ℝ) := by
    linarith
  have hsq_pos : 0 < (Real.log ((X + BankParams.H : ℕ) : ℝ)) ^ 2 := sq_pos_of_pos hlog_pos
  dsimp [convScaleLower]
  positivity

lemma convScaleLower_le_normFactor_on_window
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    convScaleLower X ≤ normFactor N := by
  have hI : N ∈ Goldbach.Windows.IccShift X BankParams.H := (Finset.mem_filter.mp hN).1
  have hN_le_XH : N ≤ X + BankParams.H :=
    N_le_X_add_H_of_mem_IccShift (X := X) (H := BankParams.H) hI
  have hX_le_N : X ≤ N := X_le_of_mem_IccShift (X := X) (H := BankParams.H) hI
  have hN0 : BankParams.X0 ≤ N := le_trans hX hX_le_N
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
  simpa [convScaleLower, normFactor] using
    mul_le_mul_of_nonneg_left hinv (by norm_num : 0 ≤ (1 / 800 : ℝ))

/--
Generic corr-integral-scale lower bound for `conv_ref`.

This is the closure surface to use once the analytic main term naturally lives on the same scale as
`corr_integral`, rather than on the deweighted `corrModelRaw` scale.
-/
theorem conv_ref_lower_of_weighted_main_gap
    (mainR : ℕ → ℕ → ℝ)
    (c0 η : ℕ → ℝ)
    (hη_lt : ∀ {X : ℕ}, BankParams.X0 ≤ X → η X < c0 X)
    (hMain :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        c0 X ≤ mainR X N)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N - (((mainR X N : ℝ)) : ℂ)‖ ≤ η X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      convScaleLower X * (c0 X - η X) ≤ Goldbach.BG_Identity.conv_ref X N := by
  intro X N hX hN
  have hrefC :
      (Goldbach.BG_Identity.conv_ref X N : ℂ) = (normFactor N : ℂ) * corr_integral X N := by
    rw [Goldbach.Cert.MajorArcAxiomsFunX.conv_ref_eq_RΛ_smooth]
    simpa [normFactor, mul_assoc, mul_left_comm, mul_comm] using
      (RΛ_smooth_cast_eq_norm_mul_corr_integral (X := X) (N := N))
  have hnf_nonneg : 0 ≤ normFactor N := by
    have hsq_nonneg : 0 ≤ (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) :=
      one_div_nonneg.mpr (sq_nonneg _)
    simpa [normFactor] using mul_nonneg (by norm_num : 0 ≤ (1 / 800 : ℝ)) hsq_nonneg
  have htarget :
      ‖(Goldbach.BG_Identity.conv_ref X N : ℂ) - (((normFactor N * mainR X N : ℝ)) : ℂ)‖
        ≤ normFactor N * η X := by
    calc
      ‖(Goldbach.BG_Identity.conv_ref X N : ℂ) - (((normFactor N * mainR X N : ℝ)) : ℂ)‖
          = ‖(normFactor N : ℂ) * (corr_integral X N - (((mainR X N : ℝ)) : ℂ))‖ := by
              rw [hrefC]
              simp [sub_eq_add_neg, add_mul, mul_comm]
      _ = normFactor N * ‖corr_integral X N - (((mainR X N : ℝ)) : ℂ)‖ := by
            rw [norm_mul]
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnf_nonneg]
      _ ≤ normFactor N * η X := mul_le_mul_of_nonneg_left (hCorr hX hN) hnf_nonneg
  have hreal_abs :
      |Goldbach.BG_Identity.conv_ref X N - normFactor N * mainR X N|
        ≤ normFactor N * η X := by
    have habs :
        |Goldbach.BG_Identity.conv_ref X N - normFactor N * mainR X N|
          = ‖(Goldbach.BG_Identity.conv_ref X N : ℂ) - (((normFactor N * mainR X N : ℝ)) : ℂ)‖ := by
      let x : ℝ := Goldbach.BG_Identity.conv_ref X N - normFactor N * mainR X N
      have hx :
          (x : ℂ) = (Goldbach.BG_Identity.conv_ref X N : ℂ) - (((normFactor N * mainR X N : ℝ)) : ℂ) := by
        simp [x]
      calc
        |Goldbach.BG_Identity.conv_ref X N - normFactor N * mainR X N| = |x| := by simp [x]
        _ = ‖x‖ := (Real.norm_eq_abs x).symm
        _ = ‖(x : ℂ)‖ := by simp
        _ = ‖(Goldbach.BG_Identity.conv_ref X N : ℂ) - (((normFactor N * mainR X N : ℝ)) : ℂ)‖ := by
              simp [hx]
    rw [habs]
    exact htarget
  have hconv_ge : normFactor N * (mainR X N - η X) ≤ Goldbach.BG_Identity.conv_ref X N := by
    have hleft := (abs_le.mp hreal_abs).1
    linarith
  have hmargin_pos : 0 < c0 X - η X := sub_pos.mpr (hη_lt hX)
  have hmargin_nonneg : 0 ≤ c0 X - η X := le_of_lt hmargin_pos
  have hmain_margin_ge : c0 X - η X ≤ mainR X N - η X := sub_le_sub_right (hMain hX hN) _
  have hscale_ge : convScaleLower X ≤ normFactor N :=
    convScaleLower_le_normFactor_on_window (X := X) (N := N) hX hN
  have hprod_le :
      convScaleLower X * (c0 X - η X) ≤ normFactor N * (mainR X N - η X) := by
    have h1 :
        convScaleLower X * (c0 X - η X) ≤ normFactor N * (c0 X - η X) := by
      exact mul_le_mul_of_nonneg_right hscale_ge hmargin_nonneg
    have h2 : normFactor N * (c0 X - η X) ≤ normFactor N * (mainR X N - η X) := by
      exact mul_le_mul_of_nonneg_left hmain_margin_ge hnf_nonneg
    exact le_trans h1 h2
  exact le_trans hprod_le hconv_ge

/-- Complex-main-term variant of `conv_ref_lower_of_weighted_main_gap`. -/
theorem conv_ref_lower_of_weighted_main_gap_re
    (mainC : ℕ → ℕ → ℂ)
    (c0 η : ℕ → ℝ)
    (hη_lt : ∀ {X : ℕ}, BankParams.X0 ≤ X → η X < c0 X)
    (hMain :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        c0 X ≤ Complex.re (mainC X N))
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N - mainC X N‖ ≤ η X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      convScaleLower X * (c0 X - η X) ≤ Goldbach.BG_Identity.conv_ref X N := by
  intro X N hX hN
  have hrefC :
      (Goldbach.BG_Identity.conv_ref X N : ℂ) = (normFactor N : ℂ) * corr_integral X N := by
    rw [Goldbach.Cert.MajorArcAxiomsFunX.conv_ref_eq_RΛ_smooth]
    simpa [normFactor, mul_assoc, mul_left_comm, mul_comm] using
      (RΛ_smooth_cast_eq_norm_mul_corr_integral (X := X) (N := N))
  have hnf_nonneg : 0 ≤ normFactor N := by
    have hsq_nonneg : 0 ≤ (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) :=
      one_div_nonneg.mpr (sq_nonneg _)
    simpa [normFactor] using mul_nonneg (by norm_num : 0 ≤ (1 / 800 : ℝ)) hsq_nonneg
  have htarget :
      ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
          - (normFactor N : ℂ) * mainC X N‖
        ≤ normFactor N * η X := by
    calc
      ‖(Goldbach.BG_Identity.conv_ref X N : ℂ) - (normFactor N : ℂ) * mainC X N‖
          = ‖(normFactor N : ℂ) * (corr_integral X N - mainC X N)‖ := by
              rw [hrefC]
              ring_nf
      _ = normFactor N * ‖corr_integral X N - mainC X N‖ := by
            rw [norm_mul]
            simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnf_nonneg]
      _ ≤ normFactor N * η X := mul_le_mul_of_nonneg_left (hCorr hX hN) hnf_nonneg
  have hreal_abs :
      |Goldbach.BG_Identity.conv_ref X N - normFactor N * Complex.re (mainC X N)|
        ≤ normFactor N * η X := by
    have hre :
        |Complex.re ((Goldbach.BG_Identity.conv_ref X N : ℂ)
            - (normFactor N : ℂ) * mainC X N)|
          ≤ ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
              - (normFactor N : ℂ) * mainC X N‖ := by
      simpa using Complex.abs_re_le_norm
        ((Goldbach.BG_Identity.conv_ref X N : ℂ) - (normFactor N : ℂ) * mainC X N)
    have hre_eq :
        Complex.re ((Goldbach.BG_Identity.conv_ref X N : ℂ)
            - (normFactor N : ℂ) * mainC X N)
          =
        Goldbach.BG_Identity.conv_ref X N - normFactor N * Complex.re (mainC X N) := by
      simp [sub_eq_add_neg, mul_comm]
    rw [hre_eq] at hre
    exact le_trans hre htarget
  have hconv_ge :
      normFactor N * (Complex.re (mainC X N) - η X) ≤ Goldbach.BG_Identity.conv_ref X N := by
    have hleft := (abs_le.mp hreal_abs).1
    linarith
  have hmargin_pos : 0 < c0 X - η X := sub_pos.mpr (hη_lt hX)
  have hmargin_nonneg : 0 ≤ c0 X - η X := le_of_lt hmargin_pos
  have hmain_margin_ge :
      c0 X - η X ≤ Complex.re (mainC X N) - η X := sub_le_sub_right (hMain hX hN) _
  have hscale_ge : convScaleLower X ≤ normFactor N :=
    convScaleLower_le_normFactor_on_window (X := X) (N := N) hX hN
  have hprod_le :
      convScaleLower X * (c0 X - η X)
        ≤ normFactor N * (Complex.re (mainC X N) - η X) := by
    have h1 :
        convScaleLower X * (c0 X - η X) ≤ normFactor N * (c0 X - η X) := by
      exact mul_le_mul_of_nonneg_right hscale_ge hmargin_nonneg
    have h2 :
        normFactor N * (c0 X - η X)
          ≤ normFactor N * (Complex.re (mainC X N) - η X) := by
      exact mul_le_mul_of_nonneg_left hmain_margin_ge hnf_nonneg
    exact le_trans h1 h2
  exact le_trans hprod_le hconv_ge

/-- Complex-main-term variant of `R_bank_lower_of_weighted_main_gap`. -/
theorem R_bank_lower_of_weighted_main_gap_re
    (mainC : ℕ → ℕ → ℂ)
    (c0 η εb : ℕ → ℝ)
    (hη_lt : ∀ {X : ℕ}, BankParams.X0 ≤ X → η X < c0 X)
    (hMain :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        c0 X ≤ Complex.re (mainC X N))
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N - mainC X N‖ ≤ η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      convScaleLower X * (c0 X - (η X + εb X)) ≤ Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  have href :
      convScaleLower X * (c0 X - η X) ≤ Goldbach.BG_Identity.conv_ref X N :=
    conv_ref_lower_of_weighted_main_gap_re
      (mainC := mainC) (c0 := c0) (η := η)
      (hη_lt := hη_lt) (hMain := hMain) (hCorr := hCorr) hX hN
  have hbridge_lower :
      Goldbach.BG_Identity.conv_ref X N - convScaleLower X * εb X
        ≤ Goldbach.BG_Identity.R_bank X N := by
    have h := (abs_le.mp (hBridge hX hN)).1
    linarith
  have hsplit :
      convScaleLower X * (c0 X - (η X + εb X))
        = convScaleLower X * (c0 X - η X) - convScaleLower X * εb X := by
    ring
  rw [hsplit]
  linarith

/-- Complex-main-term positivity consequence on the corr-integral scale. -/
theorem R_bank_pos_of_weighted_main_gap_re
    (mainC : ℕ → ℕ → ℂ)
    (c0 η εb : ℕ → ℝ)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt : ∀ {X : ℕ}, BankParams.X0 ≤ X → η X + εb X < c0 X)
    (hMain :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        c0 X ≤ Complex.re (mainC X N))
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N - mainC X N‖ ≤ η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  have hscale_pos : 0 < convScaleLower X := convScaleLower_pos hX
  have hmargin_pos : 0 < c0 X - (η X + εb X) := sub_pos.mpr (hsum_lt hX)
  have hlower :
      convScaleLower X * (c0 X - (η X + εb X)) ≤ Goldbach.BG_Identity.R_bank X N :=
    R_bank_lower_of_weighted_main_gap_re
      (mainC := mainC) (c0 := c0) (η := η) (εb := εb)
      (hη_lt := by
        intro X hX
        have hεb : 0 ≤ εb X := hεb_nonneg hX
        linarith [hsum_lt hX])
      (hMain := hMain) (hCorr := hCorr) (hBridge := hBridge) hX hN
  have hprod_pos : 0 < convScaleLower X * (c0 X - (η X + εb X)) :=
    mul_pos hscale_pos hmargin_pos
  exact lt_of_lt_of_le hprod_pos hlower


/-- Corr-integral-scale lower bound for `R_bank`, assuming a weighted main-term gap and bridge. -/
theorem R_bank_lower_of_weighted_main_gap
    (mainR : ℕ → ℕ → ℝ)
    (c0 η εb : ℕ → ℝ)
    (hη_lt : ∀ {X : ℕ}, BankParams.X0 ≤ X → η X < c0 X)
    (hMain :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        c0 X ≤ mainR X N)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N - (((mainR X N : ℝ)) : ℂ)‖ ≤ η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      convScaleLower X * (c0 X - (η X + εb X)) ≤ Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  have href :
      convScaleLower X * (c0 X - η X) ≤ Goldbach.BG_Identity.conv_ref X N :=
    conv_ref_lower_of_weighted_main_gap
      (mainR := mainR) (c0 := c0) (η := η)
      (hη_lt := hη_lt) (hMain := hMain) (hCorr := hCorr) hX hN
  have hbridge_lower :
      Goldbach.BG_Identity.conv_ref X N - convScaleLower X * εb X ≤ Goldbach.BG_Identity.R_bank X N := by
    have h := (abs_le.mp (hBridge hX hN)).1
    linarith
  have hsplit :
      convScaleLower X * (c0 X - (η X + εb X))
        = convScaleLower X * (c0 X - η X) - convScaleLower X * εb X := by
    ring
  rw [hsplit]
  linarith

/-- Positivity consequence of the corr-integral-scale closure gate. -/
theorem R_bank_pos_of_weighted_main_gap
    (mainR : ℕ → ℕ → ℝ)
    (c0 η εb : ℕ → ℝ)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt : ∀ {X : ℕ}, BankParams.X0 ≤ X → η X + εb X < c0 X)
    (hMain :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        c0 X ≤ mainR X N)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N - (((mainR X N : ℝ)) : ℂ)‖ ≤ η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  have hscale_pos : 0 < convScaleLower X := convScaleLower_pos hX
  have hmargin_pos : 0 < c0 X - (η X + εb X) := sub_pos.mpr (hsum_lt hX)
  have hlower :
      convScaleLower X * (c0 X - (η X + εb X)) ≤ Goldbach.BG_Identity.R_bank X N :=
    R_bank_lower_of_weighted_main_gap
      (mainR := mainR) (c0 := c0) (η := η) (εb := εb)
      (hη_lt := by
        intro X hX
        have hεb : 0 ≤ εb X := hεb_nonneg hX
        linarith [hsum_lt hX])
      (hMain := hMain) (hCorr := hCorr) (hBridge := hBridge) hX hN
  exact lt_of_lt_of_le (mul_pos hscale_pos hmargin_pos) hlower

/--
Generic variable-scale, variable-slack analytic hypothesis on the corr-integral closure surface.
-/
def analyticHypScaleNormEps_weighted
    (mainR : ℕ → ℕ → ℝ)
    (c0 η εb : ℕ → ℝ)
    (hc0_pos : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 < c0 X)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt : ∀ {X : ℕ}, BankParams.X0 ≤ X → η X + εb X < c0 X)
    (hMain :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        c0 X ≤ mainR X N)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N - (((mainR X N : ℝ)) : ℂ)‖ ≤ η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    Goldbach.AnalyticHypScaleNormEps
      BankParams.X0
      (fun _ => BankParams.H)
      convScaleLower
      c0
      (fun X => η X + εb X) := by
  refine Goldbach.AnalyticHypScaleNormEps.ofTenor ?_
  refine Goldbach.TenorHypScaleNormEps.mkPack
    BankParams.X0
    (fun _ => BankParams.H)
    convScaleLower
    c0
    (fun X => η X + εb X)
    ?_ ?_ ?_
    (fun X _ => convScaleLower X * c0 X)
    ?_ ?_
  · intro X hX
    exact convScaleLower_pos hX
  · intro X hX
    exact hc0_pos hX
  · intro X hX
    exact hsum_lt hX
  · intro X N hX hN
    simp [mul_comm]
  · intro X N hX hN
    have hweighted :
        convScaleLower X * (c0 X - (η X + εb X)) ≤ Goldbach.BG_Identity.R_bank X N :=
      R_bank_lower_of_weighted_main_gap
        (mainR := mainR) (c0 := c0) (η := η) (εb := εb)
        (hη_lt := by
          intro X hX
          have hεb : 0 ≤ εb X := hεb_nonneg hX
          linarith [hsum_lt hX])
        (hMain := hMain)
        (hCorr := hCorr)
        (hBridge := hBridge)
        hX hN
    have hbank :
        convScaleLower X * c0 X - (η X + εb X) * convScaleLower X
          ≤ Goldbach.BG_Identity.R_bank X N := by
      calc
        convScaleLower X * c0 X - (η X + εb X) * convScaleLower X
            = convScaleLower X * (c0 X - (η X + εb X)) := by ring
        _ ≤ Goldbach.BG_Identity.R_bank X N := hweighted
    simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using hbank

/-- Packaged pointwise witness for the corr-integral-scale closure route. -/
noncomputable def witness_weightedScaleNormEps
    (mainR : ℕ → ℕ → ℝ)
    (c0 η εb : ℕ → ℝ)
    (hc0_pos : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 < c0 X)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt : ∀ {X : ℕ}, BankParams.X0 ≤ X → η X + εb X < c0 X)
    (hMain :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        c0 X ≤ mainR X N)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral X N - (((mainR X N : ℝ)) : ℂ)‖ ≤ η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    Goldbach.Analytic.PointwiseWitnessScaleNormEps :=
  Goldbach.Analytic.PointwiseWitnessScaleNormEps.ofAnalytic
    (analyticHypScaleNormEps_weighted
      (mainR := mainR) (c0 := c0) (η := η) (εb := εb)
      (hc0_pos := hc0_pos)
      (hεb_nonneg := hεb_nonneg)
      (hsum_lt := hsum_lt)
      (hMain := hMain)
      (hCorr := hCorr)
      (hBridge := hBridge))

end

end Goldbach.BankPieces.Cert.IntegralScaleClosureGate
