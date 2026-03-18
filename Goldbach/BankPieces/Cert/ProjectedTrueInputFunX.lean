import Goldbach.AO_OffDiag.TenorHypFunX
import Goldbach.AO_OffDiag.TailBlockFunCompat
import Goldbach.BankPieces.Cert.ProjectedTrueInput
import Goldbach.BankPieces.Cert.ProjectedSigmaBridge
import Goldbach.BankPieces.Cert.RamanujanSeriesCutoffBridge
import Goldbach.BG_Bank
import Goldbach.BG_Calib
import Goldbach.Cert.CanonLogBounds
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.ProjectedTrueInputFunX

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.EntryPointTenorFunX
open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.BankPieces.Cert.ProjectedTrueInput

noncomputable section

/-- The realized true singular series, viewed as the honest `sigma` target. -/
noncomputable abbrev sigmaTrue (N : ℕ) : ℝ :=
  sigmaGlobal ramanujanSeriesGlobal ramanujanEulerProductRealization N

/-- Variable-cutoff projected truncation object on the Hardy--Littlewood `N / log^2 N` scale. -/
noncomputable def sigmaTruncProjectedFunX
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) (X N : ℕ) : ℝ :=
  TailBlockFun.sigma_trunc (Hoff.Q X) N * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)

private lemma sigmaHonest_fixed_eq_sigmaTrue {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Goldbach.AO_OffDiag.sigmaHonest N = sigmaTrue N := by
  have hN_ge_X : X ≤ N := by
    have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : X0 ≤ N := le_trans hX hN_ge_X
  have hN0 : N ≠ 0 := Nat.ne_of_gt <| lt_of_lt_of_le (by decide : 0 < X0) hN_ge_X0
  calc
    Goldbach.AO_OffDiag.sigmaHonest N
        = Goldbach.AO_OffDiag.EntryPointTenorFunX.sigmaHonest
            (fun _ => Goldbach.AO_OffDiag.TailBlock.Q0) X N := by
            simp [Goldbach.AO_OffDiag.sigmaHonest,
              Goldbach.AO_OffDiag.EntryPointTenorFunX.sigmaHonest,
              Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0,
              Goldbach.AO_OffDiag.TailBlockFun.sigma_trunc,
              Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail,
              Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTail,
              Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTerm,
              Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTerm,
              Goldbach.AO_OffDiag.TailBlock.ramanujanR,
              Goldbach.AO_OffDiag.TailBlockFun.ramanujanR,
              Goldbach.AO_OffDiag.TailBlock.ramanujanZ,
              Goldbach.AO_OffDiag.TailBlockFun.ramanujanZ,
              Goldbach.AO_OffDiag.muSq,
              Goldbach.AO_OffDiag.TailBlock.muSq,
              Goldbach.AO_OffDiag.TailBlockFun.muSq]
    _ = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N :=
          Goldbach.BankPieces.Cert.RamanujanSeriesCutoffBridge.sigmaHonest_eq_sigmaSeriesRamanujan
            (Q := fun _ => Goldbach.AO_OffDiag.TailBlock.Q0) hN0
    _ = ramanujanSeriesGlobal.sigma N := by
          symm
          exact ramanujanSeriesGlobal.sigma_eq_ramanujan_global N
    _ = sigmaTrue N := by
          symm
          exact ramanujanEulerProductRealization.sigma_eq_euler_global (Nat.pos_of_ne_zero hN0)

/-- `X`-only upper envelope for `N / log(N)^2` on the canonical window. -/
noncomputable def projectedScaleUpper (X : ℕ) : ℝ :=
  ((X + H : ℕ) : ℝ) / (Real.log (X : ℝ)) ^ 2

private lemma scale_nonneg_of_window {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    0 ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
  have hN_ge_X : X ≤ N := by
    have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : X0 ≤ N := le_trans hX hN_ge_X
  have hnum_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hlog_ge_ten : (10 : ℝ) ≤ Real.log (N : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hN_ge_X0
  have hlog_sq_nonneg : 0 ≤ (Real.log (N : ℝ)) ^ 2 := by positivity
  exact div_nonneg hnum_nonneg hlog_sq_nonneg

private lemma projectedScaleUpper_nonneg {X : ℕ} :
    0 ≤ projectedScaleUpper X := by
  have hnum_nonneg : 0 ≤ (((X + H : ℕ) : ℝ)) := by positivity
  have hden_nonneg : 0 ≤ (Real.log (X : ℝ)) ^ 2 := by positivity
  exact div_nonneg hnum_nonneg hden_nonneg

private lemma projectedScale_le_upper_on_window {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) ≤ projectedScaleUpper X := by
  have hN_ge_X : X ≤ N := by
    have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_le_XH : N ≤ X + H := by
    have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.add_le_add_left (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) X
  have hN_ge_X0 : X0 ≤ N := le_trans hX hN_ge_X
  have hlog_le : Real.log (X : ℝ) ≤ Real.log (N : ℝ) := by
    have hX_pos : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
    have hXN : (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_X
    exact Real.log_le_log hX_pos hXN
  have hlogX_nonneg : 0 ≤ Real.log (X : ℝ) := by
    have hten : (10 : ℝ) ≤ Real.log (X : ℝ) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
    linarith
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have hten : (10 : ℝ) ≤ Real.log (N : ℝ) :=
      Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hN_ge_X0
    linarith
  have hsq : (Real.log (X : ℝ)) ^ 2 ≤ (Real.log (N : ℝ)) ^ 2 := by
    have habs :
        |Real.log (X : ℝ)| ≤ |Real.log (N : ℝ)| := by
      calc
        |Real.log (X : ℝ)| = Real.log (X : ℝ) := by simp [abs_of_nonneg hlogX_nonneg]
        _ ≤ Real.log (N : ℝ) := hlog_le
        _ = |Real.log (N : ℝ)| := by simp [abs_of_nonneg hlogN_nonneg]
    exact sq_le_sq.mpr habs
  have hsqpos : 0 < (Real.log (X : ℝ)) ^ 2 := by
    have hlogX_pos : 0 < Real.log (X : ℝ) := by
      have hten : (10 : ℝ) ≤ Real.log (X : ℝ) :=
        Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
      linarith
    exact sq_pos_of_pos hlogX_pos
  have hN_cast_le : (N : ℝ) ≤ (((X + H : ℕ) : ℝ)) := by exact_mod_cast hN_le_XH
  have hinv :
      ((Real.log (N : ℝ)) ^ 2)⁻¹ ≤ ((Real.log (X : ℝ)) ^ 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hsqpos hsq
  calc
    ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)
        = (N : ℝ) * ((Real.log (N : ℝ)) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (((X + H : ℕ) : ℝ)) * ((Real.log (X : ℝ)) ^ 2)⁻¹ := by
          exact mul_le_mul hN_cast_le hinv (by positivity) (by positivity)
    _ = projectedScaleUpper X := by
          simp [projectedScaleUpper, div_eq_mul_inv]

/--
The variable-`Q(X)` honest sigma witness from `TenorHypFunX` equals the realized global Ramanujan
singular series on the canonical window.
-/
theorem sigmaHonest_eq_sigmaTrue
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      sigmaHonest Hoff.Q X N = sigmaTrue N := by
  intro X N hX hN
  have hN_ge_X : X ≤ N := by
    have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : X0 ≤ N := le_trans hX hN_ge_X
  have hN0 : N ≠ 0 := Nat.ne_of_gt <| lt_of_lt_of_le (by decide : 0 < X0) hN_ge_X0
  calc
    sigmaHonest Hoff.Q X N
        = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N :=
          Goldbach.BankPieces.Cert.RamanujanSeriesCutoffBridge.sigmaHonest_eq_sigmaSeriesRamanujan
            (Q := Hoff.Q) (X := X) (N := N) hN0
    _ = ramanujanSeriesGlobal.sigma N := by
          symm
          exact ramanujanSeriesGlobal.sigma_eq_ramanujan_global N
    _ = sigmaTrue N := by
          symm
          exact ramanujanEulerProductRealization.sigma_eq_euler_global (Nat.pos_of_ne_zero hN0)

/--
Using the existing variable-`Q(X)` FunX tail budget, compare the truncated singular-series object
directly to the honest realized singular series.
-/
theorem sigmaTrunc_vs_sigmaTrue_of_offDiagHyp
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |TailBlockFun.sigma_trunc (Hoff.Q X) N - sigmaTrue N| ≤ Hoff.eps := by
  intro X N hX hN
  have htail :
      |(Goldbach.AO_OffDiag.TenorHypFunX.model Hoff).sigma X N
          - TailBlockFun.sigma_trunc (Hoff.Q X) N| ≤ Hoff.eps :=
    Goldbach.AO_OffDiag.TenorHypFunX.tail_bound_on_window Hoff hX hN
  have hsigma_model :
      (Goldbach.AO_OffDiag.TenorHypFunX.model Hoff).sigma X N = sigmaHonest Hoff.Q X N := by
    rfl
  have hsigma :
      (Goldbach.AO_OffDiag.TenorHypFunX.model Hoff).sigma X N = sigmaTrue N := by
    rw [hsigma_model]
    exact sigmaHonest_eq_sigmaTrue Hoff hX hN
  calc
    |TailBlockFun.sigma_trunc (Hoff.Q X) N - sigmaTrue N|
        = |sigmaTrue N - TailBlockFun.sigma_trunc (Hoff.Q X) N| := by rw [abs_sub_comm]
    _ = |(Goldbach.AO_OffDiag.TenorHypFunX.model Hoff).sigma X N
            - TailBlockFun.sigma_trunc (Hoff.Q X) N| := by rw [hsigma]
    _ ≤ Hoff.eps := htail

/--
Projected Hardy--Littlewood main-term comparison on the true route, now driven by the honest
variable-`Q(X)` FunX tail infrastructure rather than the fixed-`Q0` seam.
-/
theorem sigmaTruncProjected_mainTerm_gap_of_offDiagHyp
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |sigmaTruncProjectedFunX Hoff X N - Mtrue N|
        ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Hoff.eps := by
  intro X N hX hN
  have hscale_nonneg :
      0 ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
    scale_nonneg_of_window hX hN
  have hσN :
      |TailBlockFun.sigma_trunc (Hoff.Q X) N - sigmaTrue N| ≤ Hoff.eps :=
    sigmaTrunc_vs_sigmaTrue_of_offDiagHyp Hoff hX hN
  calc
    |sigmaTruncProjectedFunX Hoff X N - Mtrue N|
        = |((N : ℝ) / (Real.log (N : ℝ)) ^ 2)
            * (TailBlockFun.sigma_trunc (Hoff.Q X) N - sigmaTrue N)| := by
            have hsplit :
                sigmaTruncProjectedFunX Hoff X N
                  - Mtrue N
                  = ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)
                      * (TailBlockFun.sigma_trunc (Hoff.Q X) N - sigmaTrue N) := by
                  simp [sigmaTruncProjectedFunX, Mtrue, ProjectedTrueInput.Mtrue, sigmaTrue,
                    sigmaGlobal, mainTermGlobal, Goldbach.MainTerm.M, div_eq_mul_inv]
                  ring
            rw [hsplit]
    _ = ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)
          * |TailBlockFun.sigma_trunc (Hoff.Q X) N - sigmaTrue N| := by
            rw [abs_mul, abs_of_nonneg hscale_nonneg]
    _ ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Hoff.eps := by
          exact mul_le_mul_of_nonneg_left hσN hscale_nonneg

/-- `X`-uniform envelope for the FunX projected main-term gap on the true route. -/
noncomputable def ΔtrueFunX
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) (X : ℕ) : ℝ :=
  projectedScaleUpper X * Hoff.eps

/-- Weighted `X`-uniform inner-swap envelope on the true projected FunX route. -/
noncomputable def constSwapGapUpperEnv [Goldbach.AO_SigmaPos.SigmaUpperOnWindow] : ℝ :=
  ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
    * (((1252 : ℝ) / 10 ^ 6)
        + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)

/-- Weighted `X`-only inner-swap envelope preserving the natural `weight_mass X` factor. -/
noncomputable def constSwapGapUpperEnvWeighted [Goldbach.AO_SigmaPos.SigmaUpperOnWindow] (X : ℕ) : ℝ :=
  Goldbach.AO_WeightMass.weight_mass X * constSwapGapUpperEnv

/--
`X`-uniform projected swap budget induced by a constant-reference comparison.

This is the honest reduction of the remaining projected swap theorem: once `conv_ref_const` is
compared to the variable-cutoff projected truncation, the `conv_ref - conv_ref_const` part is
already controlled by the weighted inner-swap bound.
-/
noncomputable def ΔswapFromConst [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    (Δconst : ℕ → ℝ) (X : ℕ) : ℝ :=
  Δconst X + constSwapGapUpperEnvWeighted X

theorem sigmaTruncProjected_mainTerm_gap_uniform_of_offDiagHyp
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |sigmaTruncProjectedFunX Hoff X N - Mtrue N| ≤ ΔtrueFunX Hoff X := by
  intro X N hX hN
  have hpoint := sigmaTruncProjected_mainTerm_gap_of_offDiagHyp Hoff hX hN
  have hscale :
      ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) ≤ projectedScaleUpper X :=
    projectedScale_le_upper_on_window hX hN
  have heps_nonneg : 0 ≤ Hoff.eps := Hoff.eps_nonneg
  calc
    |sigmaTruncProjectedFunX Hoff X N - Mtrue N|
        ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Hoff.eps := hpoint
    _ ≤ projectedScaleUpper X * Hoff.eps := by
          exact mul_le_mul_of_nonneg_right hscale heps_nonneg
    _ = ΔtrueFunX Hoff X := rfl

/-- The fixed-`Q0` staged sigma model already matches the honest true singular series up to tail. -/
theorem conv_ref_const_sigmaTrue_gap
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.BG_Identity.conv_ref_const X N
        - Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
            * Goldbach.AO_WeightMass.weight_mass X * sigmaTrue N|
      ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X := by
  have hhonest :=
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.conv_ref_const_sigmaHonest_gap
      (X := X) (N := N) hX hN
  have hsigma : Goldbach.AO_OffDiag.sigmaHonest N = sigmaTrue N :=
    sigmaHonest_fixed_eq_sigmaTrue hX hN
  simpa [Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted,
    hsigma, mul_assoc, mul_left_comm, mul_comm] using hhonest

/-- `X`-uniform constant-reference gap induced by a scale-mismatch theorem. -/
noncomputable def ΔconstFromScale
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δscale : ℕ → ℝ) (X : ℕ) : ℝ :=
  Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
    + Δscale X + ΔtrueFunX Hoff X

/--
Reduction of the true projected constant-reference gap to one explicit scale mismatch.

The fixed-`Q0` tail and variable-`Q(X)` tail are absorbed by existing proved envelopes; the only
remaining input is a comparison between the staged coefficient
`sigmaModelCoeff * weight_mass X` and the Hardy--Littlewood scale `N / log(N)^2`.
-/
theorem conv_ref_const_sigmaTruncProjected_gap_of_scale_gap
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δscale : ℕ → ℝ)
    (hScale :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |(Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
            * Goldbach.AO_WeightMass.weight_mass X
            - ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)) * sigmaTrue N|
          ≤ Δscale X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref_const X N - sigmaTruncProjectedFunX Hoff X N|
        ≤ ΔconstFromScale Hoff Δscale X := by
  intro X N hX hN
  let coeff :=
    Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaModelCoeff
      * Goldbach.AO_WeightMass.weight_mass X
  let scale := ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)
  have hfixed := conv_ref_const_sigmaTrue_gap (X := X) (N := N) hX hN
  have hscale := hScale (X := X) (N := N) hX hN
  have htrunc := sigmaTruncProjected_mainTerm_gap_uniform_of_offDiagHyp Hoff hX hN
  have hsplit :
      Goldbach.BG_Identity.conv_ref_const X N - sigmaTruncProjectedFunX Hoff X N
        = (Goldbach.BG_Identity.conv_ref_const X N - coeff * sigmaTrue N)
            + ((coeff - scale) * sigmaTrue N)
            + (Mtrue N - sigmaTruncProjectedFunX Hoff X N) := by
    dsimp [coeff, scale]
    simp [sigmaTruncProjectedFunX, Mtrue, ProjectedTrueInput.Mtrue, sigmaTrue,
      sigmaGlobal, mainTermGlobal, Goldbach.MainTerm.M, div_eq_mul_inv]
    ring
  have htri :
      |Goldbach.BG_Identity.conv_ref_const X N - sigmaTruncProjectedFunX Hoff X N|
        ≤ |Goldbach.BG_Identity.conv_ref_const X N - coeff * sigmaTrue N|
            + |(coeff - scale) * sigmaTrue N|
            + |Mtrue N - sigmaTruncProjectedFunX Hoff X N| := by
    calc
      |Goldbach.BG_Identity.conv_ref_const X N - sigmaTruncProjectedFunX Hoff X N|
          = |(Goldbach.BG_Identity.conv_ref_const X N - coeff * sigmaTrue N)
              + ((coeff - scale) * sigmaTrue N)
              + (Mtrue N - sigmaTruncProjectedFunX Hoff X N)| := by
                rw [hsplit]
      _ ≤ |(Goldbach.BG_Identity.conv_ref_const X N - coeff * sigmaTrue N)
              + ((coeff - scale) * sigmaTrue N)|
            + |Mtrue N - sigmaTruncProjectedFunX Hoff X N| := by
              simpa [add_assoc] using
                (abs_add_le
                  ((Goldbach.BG_Identity.conv_ref_const X N - coeff * sigmaTrue N)
                    + ((coeff - scale) * sigmaTrue N))
                  (Mtrue N - sigmaTruncProjectedFunX Hoff X N))
      _ ≤ (|Goldbach.BG_Identity.conv_ref_const X N - coeff * sigmaTrue N|
              + |(coeff - scale) * sigmaTrue N|)
            + |Mtrue N - sigmaTruncProjectedFunX Hoff X N| := by
              gcongr
              simpa using
                (abs_add_le
                  (Goldbach.BG_Identity.conv_ref_const X N - coeff * sigmaTrue N)
                  ((coeff - scale) * sigmaTrue N))
      _ = |Goldbach.BG_Identity.conv_ref_const X N - coeff * sigmaTrue N|
            + |(coeff - scale) * sigmaTrue N|
            + |Mtrue N - sigmaTruncProjectedFunX Hoff X N| := by ring
  have htail' :
      |Mtrue N - sigmaTruncProjectedFunX Hoff X N| ≤ ΔtrueFunX Hoff X := by
    simpa [abs_sub_comm] using htrunc
  calc
    |Goldbach.BG_Identity.conv_ref_const X N - sigmaTruncProjectedFunX Hoff X N|
        ≤ |Goldbach.BG_Identity.conv_ref_const X N - coeff * sigmaTrue N|
            + |(coeff - scale) * sigmaTrue N|
            + |Mtrue N - sigmaTruncProjectedFunX Hoff X N| := htri
    _ ≤ Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaTailWeightedEnv X
          + Δscale X + ΔtrueFunX Hoff X := by
            exact add_le_add (add_le_add hfixed hscale) htail'
    _ = ΔconstFromScale Hoff Δscale X := by
          simp [ΔconstFromScale]

/--
Reduction of the projected swap theorem to a constant-reference comparison.

This is the exact remaining normalization seam after factoring out the already-proved weighted
inner swap `conv_ref - conv_ref_const`.
-/
theorem conv_ref_sigmaTruncProjected_gap_of_const_gap
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δconst : ℕ → ℝ)
    (hConst :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_ref_const X N - sigmaTruncProjectedFunX Hoff X N|
          ≤ Δconst X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - sigmaTruncProjectedFunX Hoff X N|
        ≤ Δconst X
          + Goldbach.AO_WeightMass.weight_mass X
              * (Goldbach.BG_Bank.payload_cap X N
                  + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
              * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
  intro X N hX hN
  exact
    Goldbach.BG_Calib.ref_to_Mfun_bound_of_const_gap_weighted
      (Mfun := fun X N => sigmaTruncProjectedFunX Hoff X N)
      (X := X) (N := N) hX hN (δ := Δconst X)
      (hAO := hConst hX hN)

/-- `X`-uniform projected swap envelope induced by a constant-reference comparison. -/
theorem conv_ref_sigmaTruncProjected_gap_uniform_of_const_gap
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δconst : ℕ → ℝ)
    (hConst :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_ref_const X N - sigmaTruncProjectedFunX Hoff X N|
          ≤ Δconst X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - sigmaTruncProjectedFunX Hoff X N|
        ≤ ΔswapFromConst Δconst X := by
  intro X N hX hN
  have hbase :=
    conv_ref_sigmaTruncProjected_gap_of_const_gap Hoff Δconst hConst hX hN
  have hcap :
      Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 :=
    Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
  have hinside :
      Goldbach.BG_Bank.payload_cap X N
          + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG
        ≤ ((1252 : ℝ) / 10 ^ 6)
            + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG := by
    exact add_le_add_right hcap _
  have hmul :
      Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.BG_Bank.payload_cap X N
              + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
          * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))
        ≤ constSwapGapUpperEnvWeighted X := by
    have hratio_nonneg : 0 ≤ ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := by
      have hnum_nonneg : 0 ≤ (2 * H + 1 : ℝ) := by
        exact_mod_cast (Nat.zero_le (2 * H + 1))
      have hden_nonneg : 0 ≤ (Goldbach.BG_Identity.Ucut : ℝ) := by
        exact_mod_cast (Nat.zero_le Goldbach.BG_Identity.Ucut)
      exact div_nonneg hnum_nonneg hden_nonneg
    have hw := mul_le_mul_of_nonneg_left hinside hwm_nonneg
    have hwr := mul_le_mul_of_nonneg_right hw hratio_nonneg
    simpa [constSwapGapUpperEnvWeighted, constSwapGapUpperEnv, mul_assoc, mul_left_comm, mul_comm] using hwr
  calc
    |Goldbach.BG_Identity.conv_ref X N - sigmaTruncProjectedFunX Hoff X N|
        ≤ Δconst X
            + Goldbach.AO_WeightMass.weight_mass X
                * (Goldbach.BG_Bank.payload_cap X N
                    + Goldbach.AO_SigmaPos.SigmaUpperOnWindow.Cσ / Goldbach.BG_Identity.mass_BG)
                * ((2 * H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ)) := hbase
    _ ≤ Δconst X + constSwapGapUpperEnvWeighted X := by
          exact add_le_add_left hmul _
    _ = ΔswapFromConst Δconst X := by
          simp [ΔswapFromConst]

/--
Reference-gap route on the true variable-`Q(X)` projected scale.

The remaining input is a projected swap theorem comparing `conv_ref` directly to the
variable-cutoff projected truncation object.
-/
theorem conv_ref_mainTerm_gap_of_projected_swap
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δswap : ℕ → ℝ)
    (hSwap :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - sigmaTruncProjectedFunX Hoff X N| ≤ Δswap X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Mtrue N| ≤ Δswap X + ΔtrueFunX Hoff X := by
  intro X N hX hN
  have hswap := hSwap (X := X) (N := N) hX hN
  have htrunc := sigmaTruncProjected_mainTerm_gap_uniform_of_offDiagHyp Hoff hX hN
  have hsplit :
      Goldbach.BG_Identity.conv_ref X N - Mtrue N
        = (Goldbach.BG_Identity.conv_ref X N - sigmaTruncProjectedFunX Hoff X N)
            + (sigmaTruncProjectedFunX Hoff X N - Mtrue N) := by
    ring
  calc
    |Goldbach.BG_Identity.conv_ref X N - Mtrue N|
        = |(Goldbach.BG_Identity.conv_ref X N - sigmaTruncProjectedFunX Hoff X N)
            + (sigmaTruncProjectedFunX Hoff X N - Mtrue N)| := by rw [hsplit]
    _ ≤ |Goldbach.BG_Identity.conv_ref X N - sigmaTruncProjectedFunX Hoff X N|
          + |sigmaTruncProjectedFunX Hoff X N - Mtrue N| := by
            simpa using
              (abs_add_le
                (Goldbach.BG_Identity.conv_ref X N - sigmaTruncProjectedFunX Hoff X N)
                (sigmaTruncProjectedFunX Hoff X N - Mtrue N))
    _ ≤ Δswap X + ΔtrueFunX Hoff X := by
          exact add_le_add hswap htrunc

/-- Full true projected bank-gap envelope driven by a projected swap input and the FunX tail budget. -/
noncomputable def ΔprojFunX
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp) (Δswap : ℕ → ℝ) (X : ℕ) : ℝ :=
  Goldbach.AO_WeightMass.weight_mass X
    * (((1252 : ℝ) / 10 ^ 6)
        * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
    + (Δswap X + ΔtrueFunX Hoff X)

theorem projected_bank_gap_of_projected_swap
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δswap : ℕ → ℝ)
    (hSwap :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_ref X N - sigmaTruncProjectedFunX Hoff X N| ≤ Δswap X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Mtrue N| ≤ ΔprojFunX Hoff Δswap X := by
  intro X N hX hN
  refine Goldbach.BankPieces.Cert.ProjectedTrueInput.bank_gap
    (Δref := fun X => Δswap X + ΔtrueFunX Hoff X)
    (Δproj := ΔprojFunX Hoff Δswap)
    ?_ ?_ hX hN
  · intro X N hX hN
    exact conv_ref_mainTerm_gap_of_projected_swap Hoff Δswap hSwap hX hN
  · intro X N hX hN
    have hcap :
        Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 :=
      Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
    have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
      have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
      simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
    have hconst_nonneg : 0 ≤ (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed) := by
      have hct : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
        norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
      linarith
    have hmul :
        Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.BG_Bank.payload_cap X N
              * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
        ≤ Goldbach.AO_WeightMass.weight_mass X
            * (((1252 : ℝ) / 10 ^ 6)
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed)) := by
      have hinner := mul_le_mul_of_nonneg_right hcap hconst_nonneg
      exact mul_le_mul_of_nonneg_left hinner hwm_nonneg
    calc
      Goldbach.AO_WeightMass.weight_mass X
        * (Goldbach.BG_Bank.payload_cap X N
            * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
        + (Δswap X + ΔtrueFunX Hoff X)
          ≤ Goldbach.AO_WeightMass.weight_mass X
              * (((1252 : ℝ) / 10 ^ 6)
                  * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
              + (Δswap X + ΔtrueFunX Hoff X) := by
                exact add_le_add_right hmul _
      _ = ΔprojFunX Hoff Δswap X := by
            simp [ΔprojFunX]

/--
Projected true bank-gap route reduced to a constant-reference comparison.

This is the narrowest active theorem surface on the honest variable-`Q(X)` route before the final
direct closure inequality: the only remaining comparison input is
`conv_ref_const` vs `sigmaTruncProjectedFunX`.
-/
theorem projected_bank_gap_of_const_gap
    [Goldbach.AO_SigmaPos.SigmaUpperOnWindow]
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp)
    (Δconst : ℕ → ℝ)
    (hConst :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.BG_Identity.conv_ref_const X N - sigmaTruncProjectedFunX Hoff X N|
          ≤ Δconst X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Mtrue N|
        ≤ ΔprojFunX Hoff (ΔswapFromConst Δconst) X := by
  intro X N hX hN
  exact projected_bank_gap_of_projected_swap
    (Hoff := Hoff)
    (Δswap := ΔswapFromConst Δconst)
    (hSwap := conv_ref_sigmaTruncProjected_gap_uniform_of_const_gap Hoff Δconst hConst)
    hX hN

end

end Goldbach.BankPieces.Cert.ProjectedTrueInputFunX
