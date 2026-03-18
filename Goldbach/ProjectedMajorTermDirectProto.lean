import Mathlib
import Goldbach.AnalyticGlobalDirect
import Goldbach.AnalyticPointwiseDirect
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma
import Goldbach.Analytic.MajorBoundFromSigma
import Goldbach.Cert.CanonLogBounds
import Goldbach.Windows
import Goldbach.BankPieces.Cert.Projected
import Goldbach.BankPieces.Cert.ProjectedInput

namespace Goldbach.ProjectedMajorTermDirectProto

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic
open Goldbach.AnalyticAssemble

noncomputable section

/-- The existing global projected major-term candidate from the older Tenor stack. -/
noncomputable abbrev Mproj (_X N : ℕ) : ℝ :=
  Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric N

/--
Prototype lower term closer to the honest Hardy–Littlewood scale:
use the singular-series floor `σmin_working` together with the window-uniform factor lower bound
`N / log^2 N ≥ X / log^2 (X + H)` for `N ∈ EvenIn X H`.
-/
noncomputable def Lproj (X : ℕ) : ℝ :=
  Goldbach.Analytic.σmin_working * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)

private lemma log_sq_pos_XH {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) :
    0 < (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2 := by
  have hXH_ge_X0 : Goldbach.Analytic.X0 ≤ X + Goldbach.Analytic.H := by
    exact le_trans hX (Nat.le_add_right X Goldbach.Analytic.H)
  have hlog_ge_ten : (10 : ℝ) ≤ Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hXH_ge_X0
  have hlog_pos : 0 < Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) := by
    linarith
  exact sq_pos_of_pos hlog_pos

lemma Lproj_nonneg {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) : 0 ≤ Lproj X := by
  have hσ : 0 ≤ Goldbach.Analytic.σmin_working := by
    dsimp [Goldbach.Analytic.σmin_working]
    have hC : 0 ≤ Goldbach.Analytic.C2_numeric.C2 := le_of_lt Goldbach.Analytic.C2_numeric.pos
    nlinarith
  have hX_nonneg : 0 ≤ (X : ℝ) := by positivity
  exact mul_nonneg hσ (div_nonneg hX_nonneg (le_of_lt (log_sq_pos_XH hX)))

/-- Window-uniform lower bound for the Hardy–Littlewood scale factor. -/
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
    have hlog_pos : 0 < Real.log (N : ℝ) := by linarith
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
        |Real.log (N : ℝ)| ≤ |Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)| := by
      calc
        |Real.log (N : ℝ)| = Real.log (N : ℝ) := by simp [abs_of_nonneg hlogN_nonneg]
        _ ≤ Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ) := hlog_le
        _ = |Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)| := by
          symm
          simp [abs_of_nonneg hlogXH_nonneg']
    exact sq_le_sq.mpr habs_le
  have hinv :
      ((Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)⁻¹
        ≤ ((Real.log (N : ℝ)) ^ 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hlog_sq_pos_N hlog_sq_le
  have hX_le_N : (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_X
  calc
    ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
        = (X : ℝ) * ((Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
    _ ≤ (N : ℝ) * ((Real.log (N : ℝ)) ^ 2)⁻¹ := by
          exact mul_le_mul hX_le_N hinv (by positivity) (by positivity)
    _ = ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
          rw [div_eq_mul_inv]

/-- The projected major term dominates the corrected window-uniform lower term. -/
lemma projected_major_lower {X N : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X Goldbach.Analytic.H) :
    Lproj X ≤ Mproj X N := by
  have hσ :
      Goldbach.Analytic.σmin_working
        ≤ Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N :=
    Goldbach.Analytic.SigmaLowerOn_working.bound hX hN
  have hfac :
      ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
        ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
    factor_lower_on_window hX hN
  have hσ_nonneg : 0 ≤ Goldbach.Analytic.σmin_working := by
    dsimp [Goldbach.Analytic.σmin_working]
    have hC : 0 ≤ Goldbach.Analytic.C2_numeric.C2 := le_of_lt Goldbach.Analytic.C2_numeric.pos
    nlinarith
  have hσN_nonneg : 0 ≤ Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N := by
    have heven := Goldbach.Analytic.even_of_window hX hN
    exact le_trans
      (by nlinarith [Goldbach.Analytic.C2_numeric.pos])
      (Goldbach.Singular.sigma_floor_even (C := Goldbach.Analytic.C2_numeric) heven)
  have hfac_nonneg :
      0 ≤ ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2) := by
    exact div_nonneg (by positivity) (le_of_lt (log_sq_pos_XH hX))
  have hmul_sigma :
      Goldbach.Analytic.σmin_working
        * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
      ≤ Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
        * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2) := by
    exact mul_le_mul_of_nonneg_right hσ hfac_nonneg
  have hmul_factor :
      Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
        * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
      ≤ Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
        * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hfac hσN_nonneg
  have hmul :
      Goldbach.Analytic.σmin_working
        * ((X : ℝ) / (Real.log ((X + Goldbach.Analytic.H : ℕ) : ℝ)) ^ 2)
      ≤ Goldbach.Singular.sigma Goldbach.Analytic.C2_numeric N
        * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
    exact le_trans hmul_sigma hmul_factor
  simpa [Lproj, Mproj, Goldbach.MainTerm.M, mul_assoc, mul_left_comm, mul_comm,
    div_eq_mul_inv] using hmul

/--
Prototype direct tenor package using the projected major term and a user-supplied additive bank gap
`Δ(X)`.

This is the intended experiment target for replacing the old `cAO` lower package: all remaining
gap work is concentrated in the hypothesis `bank_gap`.
-/
def tenorHypDirect_projected
    (Δ : ℕ → ℝ)
    (gap_nonneg : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δ X)
    (gap_lt_lower : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X -> Δ X < Lproj X)
    (bank_gap :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.R_bank X N - Mproj X N| ≤ Δ X) :
    Goldbach.TenorHypDirect Goldbach.Analytic.X0
      (fun _ => Goldbach.Analytic.H) Lproj Δ :=
  Goldbach.TenorHypDirect.mkPack
    Goldbach.Analytic.X0
    (fun _ => Goldbach.Analytic.H)
    Lproj
    Δ
    gap_nonneg
    gap_lt_lower
    Mproj
    (by
      intro X N hX hN
      exact projected_major_lower hX hN)
    (by
      intro X N hX hN
      exact bank_gap hX hN)

/-- Direct analytic hypothesis induced by the projected main-term prototype. -/
def analyticHypDirect_projected
    (Δ : ℕ → ℝ)
    (gap_nonneg : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δ X)
    (gap_lt_lower : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X -> Δ X < Lproj X)
    (bank_gap :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.R_bank X N - Mproj X N| ≤ Δ X) :
    Goldbach.AnalyticHypDirect Goldbach.Analytic.X0
      (fun _ => Goldbach.Analytic.H) Lproj Δ :=
  Goldbach.AnalyticHypDirect.ofTenor
    (tenorHypDirect_projected
      (Δ := Δ)
      (gap_nonneg := gap_nonneg)
      (gap_lt_lower := gap_lt_lower)
      (bank_gap := bank_gap))

/-- Packaged pointwise witness on the direct route, once a decaying projected-gap theorem exists. -/
def pointwiseWitness_projected
    (Δ : ℕ → ℝ)
    (gap_nonneg : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X → 0 ≤ Δ X)
    (gap_lt_lower : ∀ {X : ℕ}, Goldbach.Analytic.X0 ≤ X -> Δ X < Lproj X)
    (bank_gap :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.R_bank X N - Mproj X N| ≤ Δ X) :
    Goldbach.Analytic.PointwiseWitnessDirect :=
  Goldbach.Analytic.PointwiseWitnessDirect.ofAnalytic
    (analyticHypDirect_projected
      (Δ := Δ)
      (gap_nonneg := gap_nonneg)
      (gap_lt_lower := gap_lt_lower)
      (bank_gap := bank_gap))

/--
Adapter from the refactored projected bank-gap certificate route.

This is the theorem-shaped entry point the projected direct prototype needed: once the old bank
certificate path is supplied in the new `Δproj(X)` form, it feeds directly into the projected
major-term package.
-/
theorem bank_gap_from_ref_gap
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δref Δproj : ℕ → ℝ)
    (hRef :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.conv_ref X N - Mproj X N| ≤ Δref X)
    (hCal :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
            + Δref X ≤ Δproj X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ Windows.EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Mproj X N| ≤ Δproj X := by
  intro X N hX hN
  simpa [Mproj] using
    (Goldbach.BankPieces.Cert.Projected.bank_gap
      (Δref := Δref) (Δproj := Δproj) (hRef := hRef) (hCal := hCal)
      (X := X) (N := N) hX hN)

/--
Operator-level adapter from the refactored projected bank-gap certificate route.

This is the same projected route, but stated against `bankOp_ref`, the operator that equals
`MainTerm.M C2_numeric` on the canonical window. It is the preferred theorem surface for future
normalization work because it avoids the older σ-mass wording.
-/
theorem bank_gap_from_ref_operator_gap
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δref Δproj : ℕ → ℝ)
    (hRef :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BG_Identity.conv_ref X N - Goldbach.BG_Identity.bankOp_ref X N| ≤ Δref X)
    (hCal :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
            + Δref X ≤ Δproj X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ Windows.EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Mproj X N| ≤ Δproj X := by
  intro X N hX hN
  simpa [Mproj] using
    (Goldbach.BankPieces.Cert.Projected.bank_gap_refOp
      (Δref := Δref) (Δproj := Δproj) (hRef := hRef) (hCal := hCal)
      (X := X) (N := N) hX hN)

/-- The explicit projected certificate input produced in `BankPieces.Cert.ProjectedInput`. -/
theorem bank_gap_from_actual_projected_input
    [Goldbach.BG_Calib.WeightsBridgeHyp] :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ Windows.EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Mproj X N|
          ≤ Goldbach.BankPieces.Cert.ProjectedInput.Δproj X := by
  intro X N hX hN
  simpa [Mproj] using
    (Goldbach.BankPieces.Cert.ProjectedInput.projected_bank_gap (X := X) (N := N) hX hN)

/--
Adapter from the weighted `sigmaHonest` projected gap route.

This is the sharper theorem surface now exposed by `ProjectedInput`: if the remaining normalization
input is a comparison between the weighted honest sigma model and the Hardy–Littlewood main term,
then the projected bank gap follows with envelope `ΔsigmaHonest_proj`.
-/
theorem bank_gap_from_sigmaHonest_input
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δhonest : ℕ → ℝ)
    (hHonest :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ Windows.EvenIn X Goldbach.Analytic.H →
          |Goldbach.BankPieces.Cert.ProjectedSigmaBridge.sigmaHonestWeighted X N - Mproj X N|
            ≤ Δhonest X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ Windows.EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Mproj X N|
          ≤ Goldbach.BankPieces.Cert.ProjectedInput.Δproj_sigmaHonest Δhonest X := by
  intro X N hX hN
  simpa [Mproj] using
    (Goldbach.BankPieces.Cert.ProjectedInput.projected_bank_gap_via_sigmaHonest
      (Δhonest := Δhonest) (hHonest := hHonest) (X := X) (N := N) hX hN)

end

end Goldbach.ProjectedMajorTermDirectProto
