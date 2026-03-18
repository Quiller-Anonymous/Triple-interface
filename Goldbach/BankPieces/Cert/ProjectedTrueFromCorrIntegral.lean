import Goldbach.BankPieces.Cert.ProjectedTrueInput
import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Cert.MajorArcModules.NumericFacts
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral

open Complex
open Goldbach
open Goldbach.Windows
open Goldbach.Analytic
open Goldbach.Cert.MajorArcAxiomsFunX
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.NumericFacts

noncomputable section

private lemma X_le_of_mem_IccShift {X H N : ℕ} (hN : N ∈ Goldbach.Windows.IccShift X H) : X ≤ N := by
  classical
  rcases Finset.mem_image.mp hN with ⟨k, hk, rfl⟩
  exact Nat.le_add_right X k

private lemma X0_le_of_mem_EvenIn {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) : X0 ≤ N := by
  have hIn : N ∈ Goldbach.Windows.IccShift X H := (Finset.mem_filter.mp hN).1
  exact le_trans hX (X_le_of_mem_IccShift (X := X) (H := H) (N := N) hIn)

/-- The global normalization factor relating `RΛ_smooth` to `corr_integral`. -/
private noncomputable def normFactor (N : ℕ) : ℝ :=
  (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)

/--
True projected model for the unnormalized complex correlation integral.

This is the unique on-scale model satisfying
`normFactor(N) * corrModelTrueRaw(N) = Mtrue(N)`.
-/
noncomputable def corrModelTrueRaw (N : ℕ) : ℂ :=
  (((Real.log (N : ℝ)) ^ 2 * (800 : ℝ)
      * Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℝ) : ℂ)

private lemma norm_normFactor_le (N : ℕ) (hN : X0 ≤ N) :
    ‖(normFactor N : ℂ)‖ ≤ (1 / 135200 : ℝ) := by
  have hlog : (13 : ℝ) ≤ Real.log (N : ℝ) := thirteen_le_log_of_X0_le (X := N) hN
  have hsq : (169 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
    have hlog0 : 0 ≤ Real.log (N : ℝ) := le_trans (by norm_num) hlog
    have hmul :
        (13 : ℝ) * (13 : ℝ) ≤ (Real.log (N : ℝ)) * (Real.log (N : ℝ)) :=
      mul_le_mul hlog hlog (by norm_num) hlog0
    norm_num at hmul ⊢
    simpa [pow_two] using hmul
  have hone_div : (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) ≤ (1 / 169 : ℝ) := by
    have hpos : (0 : ℝ) < (169 : ℝ) := by norm_num
    simpa using (one_div_le_one_div_of_le hpos hsq)
  have hnf_le : normFactor N ≤ (1 / 135200 : ℝ) := by
    have h' :
        normFactor N ≤ (1 / 800 : ℝ) * (1 / 169 : ℝ) := by
      have hmul :
          (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)
            ≤
          (1 / 800 : ℝ) * (1 / 169 : ℝ) :=
        mul_le_mul_of_nonneg_left hone_div (by norm_num)
      simpa [normFactor] using hmul
    have hconst : (1 / 800 : ℝ) * (1 / 169 : ℝ) = (1 / 135200 : ℝ) := by norm_num
    exact le_trans h' (le_of_eq hconst)
  have hnf0 : 0 ≤ normFactor N := by
    have : 0 ≤ (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) := by
      exact one_div_nonneg.mpr (sq_nonneg _)
    simpa [normFactor] using mul_nonneg (by norm_num : 0 ≤ (1 / 800 : ℝ)) this
  have hnorm : ‖(normFactor N : ℂ)‖ = normFactor N := by
    have habs : ‖(normFactor N : ℂ)‖ = |normFactor N| := by
      calc
        ‖(normFactor N : ℂ)‖ = ‖normFactor N‖ := by
          simpa using (Complex.norm_real (normFactor N))
        _ = |normFactor N| := Real.norm_eq_abs _
    simpa [abs_of_nonneg hnf0] using habs
  rw [hnorm]
  exact hnf_le

private lemma normFactor_mul_corrModelTrueRaw_eq_Mtrue (N : ℕ) (hN : X0 ≤ N) :
    (normFactor N : ℂ) * corrModelTrueRaw N =
      (Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℂ) := by
  have hlog : (13 : ℝ) ≤ Real.log (N : ℝ) := thirteen_le_log_of_X0_le (X := N) hN
  have hlog_ne : Real.log (N : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 13) hlog)
  have hpow_ne : (Real.log (N : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
  have hReal :
      normFactor N
        * ((Real.log (N : ℝ)) ^ 2 * (800 : ℝ)
            * Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N)
      =
      Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N := by
    set L : ℝ := (Real.log (N : ℝ)) ^ 2
    have hL : L ≠ 0 := by simpa [L] using hpow_ne
    have :
        (1 / 800 : ℝ) *
            ((1 / L : ℝ) *
              (L * ((800 : ℝ) * Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N)))
          =
        Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N := by
      simp [one_div, hL, mul_assoc, mul_left_comm, mul_comm]
    simpa [normFactor, L, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hC :
      ((normFactor N
          * ((Real.log (N : ℝ)) ^ 2 * (800 : ℝ)
              * Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N)) : ℂ)
        =
      (Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℂ) := by
    simpa using congrArg (fun r : ℝ => (r : ℂ)) hReal
  simpa [corrModelTrueRaw, mul_assoc, mul_left_comm, mul_comm] using hC

/--
Turn a direct major-arc bound for `corr_integral` against the true projected model into a banked
smooth-count bound against the honest Hardy--Littlewood main term.
-/
theorem conv_ref_mainTerm_gap_of_corr_integral_true_bound
    (ε : ℕ → ℝ)
    (hCorr :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ‖corr_integral X N - corrModelTrueRaw N‖ ≤ ε X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N|
        ≤ (1 / 135200 : ℝ) * ε X := by
  intro X N hX hN
  have hN0 : X0 ≤ N := X0_le_of_mem_EvenIn (X := X) (N := N) hX hN
  have hCorr' : ‖corr_integral X N - corrModelTrueRaw N‖ ≤ ε X := hCorr hX hN
  have hrefC :
      (Goldbach.BG_Identity.conv_ref X N : ℂ) = (normFactor N : ℂ) * corr_integral X N := by
    rw [Goldbach.Cert.MajorArcAxiomsFunX.conv_ref_eq_RΛ_smooth]
    simpa [normFactor, mul_assoc, mul_left_comm, mul_comm] using
      (RΛ_smooth_cast_eq_norm_mul_corr_integral (X := X) (N := N))
  have hmodelC :
      (Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℂ)
        = (normFactor N : ℂ) * corrModelTrueRaw N := by
    symm
    exact normFactor_mul_corrModelTrueRaw_eq_Mtrue N hN0
  have hdiffC :
      (Goldbach.BG_Identity.conv_ref X N : ℂ)
        - (Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℂ)
      =
      (normFactor N : ℂ) * (corr_integral X N - corrModelTrueRaw N) := by
    rw [hrefC, hmodelC]
    ring
  have hnf_abs : ‖(normFactor N : ℂ)‖ = |normFactor N| := by
    calc
      ‖(normFactor N : ℂ)‖ = ‖normFactor N‖ := by
        simpa using (Complex.norm_real (normFactor N))
      _ = |normFactor N| := Real.norm_eq_abs _
  have hnf_abs_le : |normFactor N| ≤ (1 / 135200 : ℝ) := by
    simpa [hnf_abs] using (norm_normFactor_le (N := N) hN0)
  have hnormC :
      ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
          - (Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℂ)‖
        ≤ (1 / 135200 : ℝ) * ε X := by
    calc
      ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
          - (Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℂ)‖
          = ‖(normFactor N : ℂ) * (corr_integral X N - corrModelTrueRaw N)‖ := by
              simpa using congrArg (fun z : ℂ => ‖z‖) hdiffC
      _ = |normFactor N| * ‖corr_integral X N - corrModelTrueRaw N‖ := by
            simpa [hnf_abs] using
              (norm_mul (normFactor N : ℂ) (corr_integral X N - corrModelTrueRaw N))
      _ ≤ (1 / 135200 : ℝ) * ‖corr_integral X N - corrModelTrueRaw N‖ := by
            exact mul_le_mul_of_nonneg_right hnf_abs_le (norm_nonneg _)
      _ ≤ (1 / 135200 : ℝ) * ε X := by
            exact mul_le_mul_of_nonneg_left hCorr' (by norm_num)
  have habs :
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N|
        =
      ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
          - (Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℂ)‖ := by
    let x : ℝ := Goldbach.BG_Identity.conv_ref X N - Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N
    have hx :
        (x : ℂ)
          = (Goldbach.BG_Identity.conv_ref X N : ℂ)
              - (Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℂ) := by
      simp [x]
    calc
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N|
          = |x| := by simp [x]
      _ = ‖x‖ := (Real.norm_eq_abs x).symm
      _ = ‖(x : ℂ)‖ := by simpa using (Complex.norm_real x).symm
      _ = ‖(Goldbach.BG_Identity.conv_ref X N : ℂ)
            - (Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N : ℂ)‖ := by
            simpa [hx]
  simpa [habs] using hnormC

/--
Bank-gap reduction from a true projected `corr_integral` bound.

This is the on-scale analogue of the older turnkey reduction, but it lands directly in the honest
Hardy--Littlewood main term `Mtrue`.
-/
theorem bank_gap_of_corr_integral_true_bound
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (ε Δproj : ℕ → ℝ)
    (hCorr :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ‖corr_integral X N - corrModelTrueRaw N‖ ≤ ε X)
    (hCal :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.BG_Bank.payload_cap X N
              * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
          + (1 / 135200 : ℝ) * ε X
          ≤ Δproj X) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N|
        ≤ Δproj X := by
  intro X N hX hN
  exact Goldbach.BankPieces.Cert.ProjectedTrueInput.bank_gap
    (Δref := fun X => (1 / 135200 : ℝ) * ε X)
    (Δproj := Δproj)
    (hRef := conv_ref_mainTerm_gap_of_corr_integral_true_bound (ε := ε) hCorr)
    (hCal := hCal)
    hX hN

end

end Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral
