import Mathlib
import Goldbach.AnalyticGlobalDirect
import Goldbach.AnalyticPointwiseDirect
import Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral
import Goldbach.BankPieces.Cert.ProjectedTrueFromQ0
import Goldbach.BankPieces.Cert.ProjectedTrueInputFunX
import Goldbach.BankPieces.Cert.TrueSingularSeries
import Goldbach.Cert.CanonLogBounds
import Goldbach.Windows

namespace Goldbach.ProjectedTrueMajorTermDirectProto

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic
open Goldbach.BankPieces.Cert.TrueSingularSeries

noncomputable section

/-- The honest projected Hardy--Littlewood main term from the realized Ramanujan singular series. -/
noncomputable abbrev Mtrue (_X N : ℕ) : ℝ :=
  mainTermGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N

/--
Window-uniform lower term built from the actual Ramanujan-series base value at `2`.

This is the true-constant analogue of `ProjectedMajorTermDirectProto.Lproj`.
-/
noncomputable def Ltrue (X : ℕ) : ℝ :=
  ramanujanSeriesGlobal.sigma 2
    * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)

private lemma log_sq_pos_XH {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) :
    0 < (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2 := by
  have hXH_ge_X0 : Goldbach.Analytic.X0 ≤ X + Goldbach.Analytic.H := by
    exact le_trans hX (Nat.le_add_right X Goldbach.Analytic.H)
  have hlog_ge_ten : (10 : ℝ) ≤ Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
  have hlog_pos : 0 < Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) := by
    linarith
  exact sq_pos_of_pos hlog_pos

lemma Ltrue_nonneg {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) : 0 ≤ Ltrue X := by
  have hbase : 0 ≤ ramanujanSeriesGlobal.sigma 2 :=
    le_of_lt ramanujanSeriesShape.base_pos
  have hX_nonneg : 0 ≤ (X : ℝ) := by positivity
  exact mul_nonneg hbase (div_nonneg hX_nonneg (le_of_lt (log_sq_pos_XH hX)))

/-- Window-uniform lower bound for the Hardy--Littlewood scale factor. -/
private lemma factor_lower_on_window {X N : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X Goldbach.Analytic.H) :
    ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
      ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
  have hN_ge_X : X ≤ N := by
    have hI : N ∈ IccShift X Goldbach.Analytic.H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_le_XH : N ≤ X + Goldbach.Analytic.H := by
    have hI : N ∈ IccShift X Goldbach.Analytic.H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.add_le_add_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) X
  have hXH_ge_X0 : Goldbach.Analytic.X0 ≤ X + Goldbach.Analytic.H := by
    exact le_trans hX (Nat.le_add_right X Goldbach.Analytic.H)
  have hN_ge_X0 : Goldbach.Analytic.X0 ≤ N := le_trans hX hN_ge_X
  have hlog_sq_pos_XH : 0 < (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2 :=
    log_sq_pos_XH hX
  have hlog_sq_pos_N : 0 < (Real.log (N : ℝ)) ^ 2 := by
    have hlog_ge_ten : (10 : ℝ) ≤ Real.log (N : ℝ) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hN_ge_X0
    have hlog_pos : 0 < Real.log (N : ℝ) := by
      linarith
    exact sq_pos_of_pos hlog_pos
  have hlog_le :
      Real.log (N : ℝ) ≤ Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) := by
    have hN_pos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < Goldbach.Analytic.X0) hN_ge_X0)
    have hcast : (N : ℝ) ≤ ((X + Goldbach.Analytic.H : ℕ) : ℝ) := by
      exact_mod_cast hN_le_XH
    exact Real.log_le_log hN_pos hcast
  have hlog_sq_le :
      (Real.log (N : ℝ)) ^ 2
        ≤ (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2 := by
    have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
      have hlog_ge_ten : (10 : ℝ) ≤ Real.log (N : ℝ) :=
        Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hN_ge_X0
      linarith
    have hlogXH_nonneg : 0 ≤ Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) := by
      have hlog_ge_ten : (10 : ℝ) ≤ Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) :=
        Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
      linarith
    have hlogXH_nonneg' : 0 ≤ Real.log ((X : ℝ) + Goldbach.Analytic.H) := by
      simpa [Nat.cast_add] using hlogXH_nonneg
    have habs_le :
        |Real.log (N : ℝ)| ≤ |Real.log ((X : ℝ) + Goldbach.Analytic.H)| := by
      calc
        |Real.log (N : ℝ)| = Real.log (N : ℝ) := by simp [abs_of_nonneg hlogN_nonneg]
        _ ≤ Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) := hlog_le
        _ = |Real.log ((X : ℝ) + Goldbach.Analytic.H)| := by
          symm
          simp [abs_of_nonneg hlogXH_nonneg', Nat.cast_add]
    have habs_le' :
        |Real.log (N : ℝ)| ≤ |Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)| := by
      simpa [Nat.cast_add] using habs_le
    exact sq_le_sq.mpr habs_le'
  have hinv :
      ((Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)⁻¹
        ≤ ((Real.log (N : ℝ)) ^ 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlog_sq_pos_N hlog_sq_le
  have hX_le_N : (X : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN_ge_X
  calc
    ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
        = (X : ℝ) * ((Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
    _ ≤ (N : ℝ) * ((Real.log (N : ℝ)) ^ 2)⁻¹ := by
          exact mul_le_mul hX_le_N hinv (by positivity) (by positivity)
    _ = ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
          rw [div_eq_mul_inv]

private lemma prod_le_prod_real {ι : Type} (s : Finset ι) (f g : ι → ℝ)
    (hf_nonneg : ∀ i ∈ s, 0 ≤ f i)
    (hg_nonneg : ∀ i ∈ s, 0 ≤ g i)
    (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  revert hf_nonneg hg_nonneg hfg
  refine Finset.induction_on s ?_ ?_
  · intro _ _ _
    simp
  · intro a s ha ih hf_nonneg hg_nonneg hfg
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hfa0 : 0 ≤ f a := hf_nonneg a (Finset.mem_insert_self a s)
    have hga0 : 0 ≤ g a := hg_nonneg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf_nonneg i (Finset.mem_insert_of_mem hi)
    have hgs : ∀ i ∈ s, 0 ≤ g i := fun i hi => hg_nonneg i (Finset.mem_insert_of_mem hi)
    have hfgs : ∀ i ∈ s, f i ≤ g i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul hfa (ih hfs hgs hfgs) (Finset.prod_nonneg hfs) hga0

/-- The realized projected major term dominates the honest window-uniform lower term. -/
lemma projected_true_major_lower {X N : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X Goldbach.Analytic.H) :
    Ltrue X ≤ Mtrue X N := by
  have hN_ge_X : X ≤ N := by
    have hI : N ∈ IccShift X Goldbach.Analytic.H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : Goldbach.Analytic.X0 ≤ N := le_trans hX hN_ge_X
  have hN_pos : 0 < N := lt_of_lt_of_le (by decide : 0 < Goldbach.Analytic.X0) hN_ge_X0
  have hEven : Even N := Goldbach.Analytic.even_of_window hX hN
  have hshape :=
    ramanujanSeriesShape.even_formula hN_pos hEven
  have hprod_ge_one :
      1 ≤ ∏ p ∈ Goldbach.Singular.oddPrimeSupport N, Goldbach.Singular.oddFactor p := by
    have hone :
        ∏ p ∈ Goldbach.Singular.oddPrimeSupport N, (1 : ℝ)
          ≤ ∏ p ∈ Goldbach.Singular.oddPrimeSupport N, Goldbach.Singular.oddFactor p := by
      exact prod_le_prod_real (Goldbach.Singular.oddPrimeSupport N)
        (fun _ => (1 : ℝ))
        Goldbach.Singular.oddFactor
        (by intro p hp; positivity)
        (by
          intro p hp
          have hp1 :=
            Goldbach.Singular.oddFactor_ge_one_of_prime_ne_two
              (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2
          linarith)
        (by
          intro p hp
          exact Goldbach.Singular.oddFactor_ge_one_of_prime_ne_two
            (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2)
    simpa using hone
  have hbase_nonneg : 0 ≤ ramanujanSeriesGlobal.sigma 2 :=
    le_of_lt ramanujanSeriesShape.base_pos
  have hsigma_lower :
      ramanujanSeriesGlobal.sigma 2 ≤ sigmaGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N := by
    calc
      ramanujanSeriesGlobal.sigma 2
          = ramanujanSeriesGlobal.sigma 2 * 1 := by ring
      _ ≤ ramanujanSeriesGlobal.sigma 2
            * ∏ p ∈ Goldbach.Singular.oddPrimeSupport N, Goldbach.Singular.oddFactor p := by
              exact mul_le_mul_of_nonneg_left hprod_ge_one hbase_nonneg
      _ = ramanujanSeriesGlobal.sigma N := by rw [← hshape]
      _ = sigmaGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N := by
            symm
            exact ramanujanEulerProductRealization.sigma_eq_euler_global hN_pos
  have hfac :=
    factor_lower_on_window hX hN
  have hsigmaN_nonneg : 0 ≤ sigmaGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N := by
    have hσeq := ramanujanEulerProductRealization.sigma_eq_euler_global hN_pos
    simp [sigmaGlobal, hσeq]
    have hshapeN := ramanujanSeriesShape.even_formula hN_pos hEven
    rw [hshapeN]
    exact mul_nonneg (le_of_lt ramanujanSeriesShape.base_pos)
      (Finset.prod_nonneg (fun p hp => le_trans (by norm_num)
        (Goldbach.Singular.oddFactor_ge_one_of_prime_ne_two
          (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2)))
  have hmul_sigma :
      ramanujanSeriesGlobal.sigma 2
        * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
      ≤ sigmaGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N
        * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2) := by
    exact mul_le_mul_of_nonneg_right hsigma_lower
      (div_nonneg (by positivity) (le_of_lt (log_sq_pos_XH hX)))
  have hmul_factor :
      sigmaGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N
        * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
      ≤ sigmaGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N
        * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hfac hsigmaN_nonneg
  have hmul :
      ramanujanSeriesGlobal.sigma 2
        * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
      ≤ sigmaGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N
        * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
    exact le_trans hmul_sigma hmul_factor
  simpa [Ltrue, Mtrue, mainTermGlobal, Goldbach.MainTerm.M, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Direct tenor package using the realized projected major term and an additive bank gap `Δ(X)`. -/
def tenorHypDirect_true_projected
    (Δ : ℕ → ℝ)
    (gap_nonneg : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δ X)
    (gap_lt_lower : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → Δ X < Ltrue X)
    (bank_gap :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.R_bank X N - Mtrue X N| ≤ Δ X) :
    Goldbach.TenorHypDirect Goldbach.Analytic.X0
      (fun _ => Goldbach.Analytic.H) Ltrue Δ :=
  Goldbach.TenorHypDirect.mkPack
    Goldbach.Analytic.X0
    (fun _ => Goldbach.Analytic.H)
    Ltrue
    Δ
    gap_nonneg
    gap_lt_lower
    Mtrue
    (by
      intro X N hX hN
      exact projected_true_major_lower hX hN)
    (by
      intro X N hX hN
      exact bank_gap hX hN)

/-- Direct analytic hypothesis induced by the realized projected major-term route. -/
def analyticHypDirect_true_projected
    (Δ : ℕ → ℝ)
    (gap_nonneg : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δ X)
    (gap_lt_lower : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → Δ X < Ltrue X)
    (bank_gap :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.R_bank X N - Mtrue X N| ≤ Δ X) :
    Goldbach.AnalyticHypDirect Goldbach.Analytic.X0
      (fun _ => Goldbach.Analytic.H) Ltrue Δ :=
  Goldbach.AnalyticHypDirect.ofTenor
    (tenorHypDirect_true_projected
      (Δ := Δ)
      (gap_nonneg := gap_nonneg)
      (gap_lt_lower := gap_lt_lower)
      (bank_gap := bank_gap))

/-- Packaged pointwise witness on the direct route for the true projected major term. -/
def pointwiseWitness_true_projected
    (Δ : ℕ → ℝ)
    (gap_nonneg : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δ X)
    (gap_lt_lower : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → Δ X < Ltrue X)
    (bank_gap :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.R_bank X N - Mtrue X N| ≤ Δ X) :
    Goldbach.Analytic.PointwiseWitnessDirect :=
  Goldbach.Analytic.PointwiseWitnessDirect.ofAnalytic
    (analyticHypDirect_true_projected
      (Δ := Δ)
      (gap_nonneg := gap_nonneg)
      (gap_lt_lower := gap_lt_lower)
      (bank_gap := bank_gap))

/--
Adapter from the honest variable-`Q(X)` FunX projected route.

The remaining projected normalization input is now a direct swap theorem between `conv_ref` and the
variable-cutoff projected truncation object.
-/
theorem bank_gap_from_funX_projected_swap_input
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δswap : ℕ → ℝ)
    (hSwap :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.conv_ref X N
              - Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTruncProjectedFunX Hoff X N|
            ≤ Δswap X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ Windows.EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Mtrue X N|
          ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔprojFunX Hoff Δswap X := by
  intro X N hX hN
  simpa [Mtrue, Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue] using
    (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.projected_bank_gap_of_projected_swap
      (Hoff := Hoff) (Δswap := Δswap) (hSwap := hSwap) (X := X) (N := N) hX hN)

/--
Narrower adapter from the honest variable-`Q(X)` route, reduced to a constant-reference gap.

This isolates the remaining normalization content to the comparison
`conv_ref_const` vs `sigmaTruncProjectedFunX`.
-/
theorem bank_gap_from_funX_const_gap_input
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δconst : ℕ → ℝ)
    (hConst :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.conv_ref_const X N
              - Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTruncProjectedFunX Hoff X N|
            ≤ Δconst X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ Windows.EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Mtrue X N|
          ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔprojFunX Hoff
              (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔswapFromConst Δconst) X := by
  intro X N hX hN
  simpa [Mtrue, Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue] using
    (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.projected_bank_gap_of_const_gap
      (Hoff := Hoff) (Δconst := Δconst) (hConst := hConst) (X := X) (N := N) hX hN)

/--
Sharpest current adapter on the honest variable-`Q(X)` true route.

The remaining normalization input is now only the scale mismatch between the staged coefficient
`sigmaModelCoeff * weight_mass X` and the Hardy--Littlewood factor `N / log(N)^2`.
-/
theorem bank_gap_from_funX_scale_gap_input
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δscale : ℕ → ℝ)
    (hScale :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |(Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
              * Goldbach.AO_WeightMass.weight_mass X
              - ((N : ℝ) / (Real.log (N : ℝ)) ^ 2))
            * Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.sigmaTrue N|
            ≤ Δscale X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ Windows.EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Mtrue X N|
          ≤ Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔprojFunX Hoff
              (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔswapFromConst
                (Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔconstFromScale Hoff Δscale)) X := by
  intro X N hX hN
  exact bank_gap_from_funX_const_gap_input
    (Hoff := Hoff)
    (Δconst := Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.ΔconstFromScale Hoff Δscale)
    (hConst :=
      Goldbach.BankPieces.Cert.ProjectedTrueInputFunX.conv_ref_const_sigmaTruncProjected_gap_of_scale_gap
        (Hoff := Hoff) (Δscale := Δscale) (hScale := hScale))
    (X := X) (N := N) hX hN

/--
On-scale major-arc reduction from the complex correlation integral.

This is the clean true-normalization analogue of the old turnkey reduction: if `corr_integral`
is directly bounded against the honest projected model `corrModelTrueRaw`, then the banked
representation gap against `Mtrue` follows with only the usual weighted bridge cost.
-/
theorem bank_gap_from_corr_integral_true_input
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (ε Δproj : ℕ → ℝ)
    (hCorr :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
              - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖
            ≤ ε X)
    (hCal :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
            + (1 / 135200 : ℝ) * ε X
            ≤ Δproj X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ Windows.EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Mtrue X N| ≤ Δproj X := by
  intro X N hX hN
  simpa [Mtrue, Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue] using
    (Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.bank_gap_of_corr_integral_true_bound
      (ε := ε) (Δproj := Δproj) (hCorr := hCorr) (hCal := hCal) (X := X) (N := N) hX hN)

/--
True projected direct-route adapter from the natural `Q0` split.

This states the remaining analytic target in the same two-piece language as the old turnkey route,
but with the second piece measured against the honest projected model instead of `corrModel`.
-/
theorem bank_gap_from_q0_true_input
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δ : ℝ)
    (ε₁ ε₂ Δproj : ℕ → ℝ)
    (hMinor :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
              - Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral_major_Q0 X N Δ‖
            ≤ ε₁ X)
    (hMajor :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral_major_Q0 X N Δ
              - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖
            ≤ ε₂ X)
    (hCal :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
            + (1 / 135200 : ℝ) * (ε₁ X + ε₂ X)
            ≤ Δproj X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ Windows.EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Mtrue X N| ≤ Δproj X := by
  intro X N hX hN
  simpa [Mtrue, Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue] using
    (Goldbach.BankPieces.Cert.ProjectedTrueFromQ0.bank_gap_of_q0_two_bounds
      (Δ := Δ) (ε₁ := ε₁) (ε₂ := ε₂) (Δproj := Δproj)
      (h₁ := hMinor) (h₂ := hMajor) (hCal := hCal)
      (X := X) (N := N) hX hN)

end

end Goldbach.ProjectedTrueMajorTermDirectProto
