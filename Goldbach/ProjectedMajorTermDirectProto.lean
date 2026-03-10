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
Prototype lower term closer to the Tenor statement: a positive `log^{-2}`-scale floor obtained by
combining the working singular-series lower bound with the crude factor bound
`N / log^2 N ≥ 1` on the working window.
-/
noncomputable def Lproj (X : ℕ) : ℝ :=
  Goldbach.Analytic.σmin_working / (Real.log (X : ℝ)) ^ 2

private lemma log_sq_pos {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) :
    0 < (Real.log (X : ℝ)) ^ 2 := by
  have hlog_ge_ten : (10 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    linarith
  exact sq_pos_of_pos hlog_pos

lemma Lproj_nonneg {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) : 0 ≤ Lproj X := by
  have hσ : 0 ≤ Goldbach.Analytic.σmin_working := by
    dsimp [Goldbach.Analytic.σmin_working]
    have hC : 0 ≤ Goldbach.Analytic.C2_numeric.C2 := le_of_lt Goldbach.Analytic.C2_numeric.pos
    nlinarith
  exact div_nonneg hσ (le_of_lt (log_sq_pos hX))

lemma Lproj_le_sigma_floor {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) :
    Lproj X ≤ Goldbach.Analytic.σmin_working := by
  have hσ : 0 ≤ Goldbach.Analytic.σmin_working := by
    dsimp [Goldbach.Analytic.σmin_working]
    have hC : 0 ≤ Goldbach.Analytic.C2_numeric.C2 := le_of_lt Goldbach.Analytic.C2_numeric.pos
    nlinarith
  have hlog_ge_ten : (10 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
  have hsq_ge_one : (1 : ℝ) ≤ (Real.log (X : ℝ)) ^ 2 := by
    nlinarith
  simpa [Lproj] using div_le_self hσ hsq_ge_one

/--
On the canonical working window, the projected `log^{-2}` lower term is strictly below the old
constant bank gap `0.01`.

So the legacy certificate layer around `MainTerm.M C2_numeric` cannot be reused unchanged for the
new direct route: a constant-gap certificate is too coarse even before any comparison with `R_bank`.
-/
lemma Lproj_lt_old_gap_on_window {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) :
    Lproj X < (0.01 : ℝ) := by
  have hlog_ge_ten : (10 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.CanonLogBounds.ten_le_log_of_X0_le hX
  have hsq_ge_hundred : (100 : ℝ) ≤ (Real.log (X : ℝ)) ^ 2 := by
    nlinarith
  have hσ_nonneg : 0 ≤ Goldbach.Analytic.σmin_working := by
    dsimp [Goldbach.Analytic.σmin_working]
    have hC : 0 ≤ Goldbach.Analytic.C2_numeric.C2 := le_of_lt Goldbach.Analytic.C2_numeric.pos
    nlinarith
  have hdiv :
      Lproj X ≤ Goldbach.Analytic.σmin_working / 100 := by
    have hdiv_raw :
        Goldbach.Analytic.σmin_working / (Real.log (X : ℝ)) ^ 2
          ≤ Goldbach.Analytic.σmin_working / 100 := by
      exact div_le_div_of_nonneg_left hσ_nonneg (by positivity) hsq_ge_hundred
    simpa [Lproj] using hdiv_raw
  have hnum : Goldbach.Analytic.σmin_working / 100 < (0.01 : ℝ) := by
    norm_num [Goldbach.Analytic.σmin_working, Goldbach.Analytic.C2_numeric]
  exact lt_of_le_of_lt hdiv hnum

/-- The projected major term already dominates the singular-series floor on the working window. -/
lemma sigma_floor_le_Mproj {X N : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X Goldbach.Analytic.H) :
    Goldbach.Analytic.σmin_working ≤ Mproj X N := by
  let hmajor :
      MajorBound Goldbach.Analytic.X0 Goldbach.Analytic.H (1 : ℝ)
        Goldbach.Analytic.σmin_working
        (Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric) :=
    Goldbach.Analytic.major_of_sigma_lower_S1
      (A := Goldbach.Analytic.SigmaLowerOn_working)
      (hc0 := le_rfl)
      (two_le_of_mem := Goldbach.Analytic.two_le_of_window)
  simpa [Mproj] using hmajor hX hN

/--
The projected lower package is genuinely different from the banked `cAO` route: it lowers directly
against the global projected main term `MainTerm.M C2_numeric`.
-/
lemma projected_major_lower {X N : ℕ}
    (hX : Goldbach.Analytic.X0 ≤ X)
    (hN : N ∈ Windows.EvenIn X Goldbach.Analytic.H) :
    Lproj X ≤ Mproj X N := by
  exact le_trans (Lproj_le_sigma_floor hX) (sigma_floor_le_Mproj hX hN)

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
The legacy constant-gap certificate shape `Δ(X) = 0.01` cannot satisfy the positivity side of the
new projected direct route on the canonical window.
-/
theorem not_old_constant_gap_lt_Lproj {X : ℕ} (hX : Goldbach.Analytic.X0 ≤ X) :
    ¬ (0.01 : ℝ) < Lproj X := by
  exact not_lt_of_ge (Lproj_lt_old_gap_on_window hX).le

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

end

end Goldbach.ProjectedMajorTermDirectProto
