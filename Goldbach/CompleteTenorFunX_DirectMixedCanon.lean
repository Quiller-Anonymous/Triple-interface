import Goldbach.CompleteTenorFunX_Direct
import Goldbach.ParallelFunXCanonScaleObstacle
import Goldbach.AO_OffDiag.WeightMass
import Goldbach.Cert.InnerSwapTextbookRoute
import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.Cert.MajorArcCanonicalCalibrationOffline
import Goldbach.Cert.SigmaLowerOnWindowCanonSpec

namespace Goldbach.ParallelTenorFunXDirectMixedCanon

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

noncomputable section

/-- Canonical bundled off-diagonal package. -/
noncomputable abbrev Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp :=
  Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff

/-- Canonical major-arc inner-swap datum from the current offline calibration route. -/
noncomputable def inner : Goldbach.ParallelTenorFunX.InnerSwapOnWindow := by
  let hcal : Goldbach.Cert.MajorArcAxiomsFunX.MajorArcBound (fun _X =>
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon) :=
    Goldbach.Cert.MajorArcCalibrationFunX.majorArcBound_canon_of_calibration
      Goldbach.Cert.MajorArcCanonicalCalibrationOffline.canonCalibration
  exact
    Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_RL_bound
      (A := 0) (C := Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon)
      (by norm_num [Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon])
      (by
        intro X N hX hN
        simpa using (hcal (X := X) (N := N) hX hN))

/-- Canonical mixed-gap expression with the pinned major-arc calibration inserted. -/
noncomputable def mixedGap (X N : ℕ) : ℝ :=
  @Goldbach.ParallelTenorFunXDirect.mixedGap Hoff inner X N

/--
Canonical semimixed-gap expression with the Mellin term supplied through `δ_mellin_window`.

This is the canonical consumer of the Mellin refactor seam.
-/
noncomputable def semimixedGap (X N : ℕ) : ℝ :=
  @Goldbach.ParallelTenorFunXDirect.semimixedGap Hoff inner
    Goldbach.AO_MellinTrunc.δ_mellin_window X N

/-- Canonical lower-term candidate for the mixed direct route. -/
noncomputable abbrev L_canon [Goldbach.AO_SigmaPos.SigmaLowerOnWindow] (X : ℕ) : ℝ :=
  Goldbach.ParallelTenorFunXDirect.cAO Hoff X

/-- Canonical additive gap candidate for the mixed direct route. -/
noncomputable def Δ_canon (_X : ℕ) : ℝ := Goldbach.CanonParams.ε

private lemma semimixedGap_le_mixedGap (X N : ℕ) :
    semimixedGap X N ≤ mixedGap X N := by
  dsimp [semimixedGap, mixedGap, Goldbach.ParallelTenorFunXDirect.semimixedGap,
    Goldbach.ParallelTenorFunXDirect.mixedGap]
  have hδ : Goldbach.AO_MellinTrunc.δ_mellin_window X ≤ Goldbach.AO_MellinTrunc.δ_mellin_canon :=
    Goldbach.AO_MellinTrunc.δ_mellin_window_le_canon X
  linarith

private lemma X_le_of_mem_EvenIn {X N H : ℕ} (hN : N ∈ EvenIn X H) : X ≤ N := by
  have hI : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
  rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
  exact Nat.le_add_right X k

private lemma payload_cap_mul_C_tail_le
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 := by
  have hcap : Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 :=
    Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
  have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
    norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
  have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
    nlinarith [htail_val]
  have hprod :
      Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed
        ≤ ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed :=
    mul_le_mul_of_nonneg_right hcap htail_nonneg
  have hnum : ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 := by
    nlinarith [htail_val]
  exact le_trans hprod hnum

private lemma delta_major_eq_canon (X : ℕ) :
    @Goldbach.ParallelTenorFunX.δ_major inner X =
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
  simp [Goldbach.ParallelTenorFunX.δ_major, inner,
    Goldbach.Cert.InnerSwapTextbookRoute.innerSwapOnWindow_of_RL_bound,
    Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon]

private lemma bridge_piece_le_deltabridge
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ((3 : ℝ) / 1000)
        * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
      ≤ Goldbach.BG_Calib.δbridge_canon := by
  have hwm_abs := Goldbach.AO_OffDiag.weight_mass_abs_le_one_on_window_canon (X := X) hX
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    simpa [Goldbach.AO_WeightMass.weight_mass] using
      (sq_nonneg (Goldbach.BG_Bank.wScale X))
  have hwm_le_one : Goldbach.AO_WeightMass.weight_mass X ≤ 1 := by
    simpa [abs_of_nonneg hwm_nonneg] using hwm_abs
  have hcap : Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 :=
    Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN
  have hcap_nonneg : 0 ≤ Goldbach.BG_Bank.payload_cap X N := by
    have := Goldbach.BG_Bank.payload_nonneg (X := X) (N := N)
    simpa using this
  have hmul :
      Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N
        ≤ (1252 : ℝ) / 10 ^ 6 := by
    have h1 :
        Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N
          ≤ 1 * Goldbach.BG_Bank.payload_cap X N := by
      exact mul_le_mul_of_nonneg_right hwm_le_one hcap_nonneg
    have h2 : 1 * Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 := by
      simpa using hcap
    exact le_trans h1 h2
  have hconst : 0 ≤ (3 : ℝ) / 1000 := by norm_num
  have hnum :
      ((3 : ℝ) / 1000) * ((1252 : ℝ) / 10 ^ 6) ≤ Goldbach.BG_Calib.δbridge_canon := by
    norm_num [Goldbach.BG_Calib.δbridge_canon]
  exact le_trans (mul_le_mul_of_nonneg_left hmul hconst) hnum

private lemma mixedGap_le_ε
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    mixedGap X N ≤ Goldbach.CanonParams.ε := by
  have hXN : X ≤ N := X_le_of_mem_EvenIn (X := X) (N := N) (H := H) hN
  have hN0 : X0 ≤ N := le_trans hX hXN
  have hwmX_abs := Goldbach.AO_OffDiag.weight_mass_abs_le_one_on_window_canon (X := X) hX
  have hwmN_abs := Goldbach.AO_OffDiag.weight_mass_abs_le_one_on_window_canon (X := N) hN0
  have hwmX_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    simpa [Goldbach.AO_WeightMass.weight_mass] using
      (sq_nonneg (Goldbach.BG_Bank.wScale X))
  have hwmN_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass N := by
    simpa [Goldbach.AO_WeightMass.weight_mass] using
      (sq_nonneg (Goldbach.BG_Bank.wScale N))
  have hwmX_le_one : Goldbach.AO_WeightMass.weight_mass X ≤ 1 := by
    simpa [abs_of_nonneg hwmX_nonneg] using hwmX_abs
  have hwmN_le_one : Goldbach.AO_WeightMass.weight_mass N ≤ 1 := by
    simpa [abs_of_nonneg hwmN_nonneg] using hwmN_abs
  have htail_abs :
      Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 7 :=
    payload_cap_mul_C_tail_le (X := X) (N := N) hX hN
  have htail_abs_nonneg : 0 ≤ Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed := by
    have hcap_nonneg := Goldbach.BG_Bank.payload_nonneg (X := X) (N := N)
    have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
      norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
    have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
      nlinarith [htail_val]
    exact mul_nonneg hcap_nonneg htail_nonneg
  have htail_weighted :
      Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
        ≤ (2 : ℝ) / 10 ^ 7 := by
    have h1 :
        Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          ≤ 1 * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) := by
      exact mul_le_mul_of_nonneg_right hwmX_le_one htail_abs_nonneg
    have h2 : 1 * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          ≤ (2 : ℝ) / 10 ^ 7 := by
      simpa using htail_abs
    exact le_trans h1 h2
  have hkernel_const_nonneg :
      0 ≤ ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed := by
    have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
      norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
    nlinarith [htail_val]
  have hkernel_weighted :
      Goldbach.AO_WeightMass.weight_mass N
          * (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed)
        ≤ ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed := by
    have h1 :
        Goldbach.AO_WeightMass.weight_mass N
            * (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed)
          ≤ 1 * (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed) := by
      exact mul_le_mul_of_nonneg_right hwmN_le_one hkernel_const_nonneg
    simpa using h1
  have hoff_nonneg : 0 ≤ Hoff.eps := Hoff.eps_nonneg
  have hoff_weighted :
      Goldbach.AO_WeightMass.weight_mass X * Hoff.eps ≤ Hoff.eps := by
    have h1 : Goldbach.AO_WeightMass.weight_mass X * Hoff.eps ≤ 1 * Hoff.eps := by
      exact mul_le_mul_of_nonneg_right hwmX_le_one hoff_nonneg
    simpa using h1
  have hbridge :
      ((3 : ℝ) / 1000)
          * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
        ≤ Goldbach.BG_Calib.δbridge_canon :=
    bridge_piece_le_deltabridge (X := X) (N := N) hX hN
  have hnum :
      Goldbach.BG_Calib.δbridge_canon
        + (2 : ℝ) / 10 ^ 7
        + Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon
        + Goldbach.AO_MellinTrunc.δ_mellin_canon
        + (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed)
        + Hoff.eps
        ≤ Goldbach.CanonParams.ε := by
    have hCtail : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
      norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
    rw [hCtail]
    dsimp [Hoff, Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff,
      Goldbach.AO_OffDiag.TenorHypFunX.Canon.eps,
      Goldbach.Cert.OffDiagBudgetAxiomsFun.eps_canon, Goldbach.CanonParams.ε,
      Goldbach.AO_MellinTrunc.δ_mellin_canon, Goldbach.AO_MellinTrunc.mellinScale,
      Goldbach.AO_MellinTrunc.eps_canon,
      Goldbach.AO_MellinTrunc.C_K_canon, Goldbach.AO_MellinTrunc.T_canon,
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon]
    norm_num [Goldbach.BG_Calib.δbridge_canon]
  have hδmajor :
      @Goldbach.ParallelTenorFunX.δ_major inner X =
        Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon :=
    delta_major_eq_canon X
  calc
    mixedGap X N
        ≤ Goldbach.BG_Calib.δbridge_canon
          + (2 : ℝ) / 10 ^ 7
          + Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon
          + Goldbach.AO_MellinTrunc.δ_mellin_canon
          + (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed)
          + Hoff.eps := by
          rw [mixedGap, Goldbach.ParallelTenorFunXDirect.mixedGap, hδmajor]
          have hleft :
              ((3 : ℝ) / 1000)
                  * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N)
                + (Goldbach.AO_WeightMass.weight_mass X
                    * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed))
              ≤ Goldbach.BG_Calib.δbridge_canon + (2 : ℝ) / 10 ^ 7 := by
            exact add_le_add hbridge htail_weighted
          have hright :
              Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon
                  + Goldbach.AO_MellinTrunc.δ_mellin_canon
                  + Goldbach.AO_WeightMass.weight_mass N
                      * (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed)
                  + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps
              ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon
                  + Goldbach.AO_MellinTrunc.δ_mellin_canon
                  + (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed)
                  + Hoff.eps := by
            have htail2 :
                Goldbach.AO_WeightMass.weight_mass N
                    * (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed)
                  + Goldbach.AO_WeightMass.weight_mass X * Hoff.eps
                ≤ (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed) + Hoff.eps := by
              exact add_le_add hkernel_weighted hoff_weighted
            linarith
          linarith
    _ ≤ Goldbach.CanonParams.ε := hnum

/-- The canonical mixed direct-gap candidate is just the existing closure tolerance `ε`. -/
theorem mixedGap_le_Δ_canon
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    mixedGap X N ≤ Δ_canon X := by
  simpa [Δ_canon] using mixedGap_le_ε (X := X) (N := N) hX hN

/-- The semimixed canonical gap satisfies the same closure budget. -/
theorem semimixedGap_le_Δ_canon
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    semimixedGap X N ≤ Δ_canon X := by
  exact le_trans (semimixedGap_le_mixedGap X N)
    (mixedGap_le_Δ_canon (X := X) (N := N) hX hN)

/--
The semimixed canonical gap still contains `δ_major_canon` as an explicit nonnegative summand.

So any attempt to close the direct route by squeezing only the other semimixed terms is limited by
the comparison between `δ_major_canon` and the AO lower package `cAO(X)`.
-/
theorem delta_major_le_semimixedGap (X N : ℕ) :
    Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon ≤ semimixedGap X N := by
  have hδm : 0 ≤ Goldbach.AO_MellinTrunc.δ_mellin_window X :=
    Goldbach.AO_MellinTrunc.δ_mellin_window_nonneg X
  have hwmX : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    simpa [Goldbach.AO_WeightMass.weight_mass] using
      (sq_nonneg (Goldbach.BG_Bank.wScale X))
  have hwmN : 0 ≤ Goldbach.AO_WeightMass.weight_mass N := by
    simpa [Goldbach.AO_WeightMass.weight_mass] using
      (sq_nonneg (Goldbach.BG_Bank.wScale N))
  have hcap : 0 ≤ Goldbach.BG_Bank.payload_cap X N := Goldbach.BG_Bank.payload_nonneg (X := X) (N := N)
  have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
    norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
  have htail : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
    nlinarith [htail_val]
  have hkernel_const : 0 ≤ (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed) := by
    have hconst : 0 ≤ ((1252 : ℝ) / 10 ^ 6) := by norm_num
    exact mul_nonneg hconst htail
  have hbridge_term :
      0 ≤ ((3 : ℝ) / 1000)
        * (Goldbach.AO_WeightMass.weight_mass X * Goldbach.BG_Bank.payload_cap X N) := by
    have hconst : 0 ≤ ((3 : ℝ) / 1000) := by norm_num
    exact mul_nonneg hconst (mul_nonneg hwmX hcap)
  have htail_term :
      0 ≤ Goldbach.AO_WeightMass.weight_mass X
        * (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed) := by
    exact mul_nonneg hwmX (mul_nonneg hcap htail)
  have hkernel_term :
      0 ≤ Goldbach.AO_WeightMass.weight_mass N
        * (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed) := by
    exact mul_nonneg hwmN hkernel_const
  have hoff_nonneg : 0 ≤ Hoff.eps := Hoff.eps_nonneg
  have hoff_term :
      0 ≤ Goldbach.AO_WeightMass.weight_mass X * Hoff.eps := by
    exact mul_nonneg hwmX hoff_nonneg
  have hδmajor :
      @Goldbach.ParallelTenorFunX.δ_major inner X =
        Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon :=
    delta_major_eq_canon X
  rw [semimixedGap, Goldbach.ParallelTenorFunXDirect.semimixedGap, hδmajor]
  nlinarith

/--
The instantiated canonical mixed direct route still fails the positivity check.

Even with the more honest mixed-gap bookkeeping, the candidate lower term `cAO(X)` remains below the
canonical gap budget `Δ_canon(X) = ε` on the canonical window.
-/
theorem not_gap_lt_lower_canon
    {X : ℕ} (hX : X0 ≤ X) :
    ¬ Δ_canon X < L_canon X := by
  letI : Goldbach.AO_SigmaPos.SigmaLowerOnWindow :=
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigmaLowerOnWindow_canon
  have hnot :
      ¬ Goldbach.CanonParams.ε < Goldbach.ParallelFunXCanonScale.c0 X :=
    Goldbach.ParallelFunXCanonScaleObstacle.not_eps_lt_c0_on_window (X := X) hX
  simpa [Δ_canon, L_canon, Goldbach.ParallelFunXCanonScale.c0,
    Goldbach.ParallelTenorFunXScale.c0, Goldbach.ParallelTenorFunXDirect.cAO,
    Goldbach.ParallelFunXCanonScale.Hoff, Hoff] using hnot

/--
The direct canonical route still does not close even if we compare against the actual semimixed gap
instead of the coarser budget `Δ_canon = ε`.
-/
theorem not_semimixedGap_lt_lower_canon
    {X N : ℕ} (hX : X0 ≤ X) :
    ¬ semimixedGap X N < L_canon X := by
  letI : Goldbach.AO_SigmaPos.SigmaLowerOnWindow :=
    Goldbach.Cert.SigmaLowerOnWindowCanonSpec.sigmaLowerOnWindow_canon
  have hgap :
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon ≤ semimixedGap X N :=
    delta_major_le_semimixedGap X N
  have hlower :
      L_canon X < Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
    simpa [L_canon, Goldbach.ParallelFunXCanonScale.c0,
      Goldbach.ParallelTenorFunXScale.c0, Goldbach.ParallelTenorFunXDirect.cAO,
      Goldbach.ParallelFunXCanonScale.Hoff, Hoff] using
      (Goldbach.ParallelFunXCanonScaleObstacle.c0_lt_delta_major_on_window (X := X) hX)
  exact not_lt_of_ge (le_trans hlower.le hgap)

/--
Any canonical lower-term package that still factors through `cAO(X)` is blocked against the
semimixed direct route.

So testing more `L(X)` variants is only meaningful if they stop satisfying `L(X) ≤ cAO(X)`.
-/
theorem not_semimixedGap_lt_of_le_lower_canon
    {L : ℕ → ℝ} {X N : ℕ} (hX : X0 ≤ X)
    (hL : L X ≤ L_canon X) :
    ¬ semimixedGap X N < L X := by
  intro hgap
  exact not_semimixedGap_lt_lower_canon (X := X) (N := N) hX (lt_of_lt_of_le hgap hL)

end
