import Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral
import Goldbach.BankPieces.Cert.ProjectedConstGapBridge
import Goldbach.Cert.MajorArcModules.MainTermQ0
import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
import Goldbach.Cert.MajorArcModules.CorrModel
import Goldbach.Cert.MajorArcModules.Q0MajorRoute
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic

namespace Goldbach.BankPieces.Cert.ProjectedTrueFromQ0

open Goldbach
open Goldbach.Windows
open Goldbach.Cert.MajorArcModules.MainTermQ0
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.Q0MajorRoute

noncomputable section

/--
Raw Step-24 extracted projected main term on the unnormalized `corr_integral` scale.

This is the correct `Q0`-major-arc target before inserting the true singular-series tail:
`qa_mainTerm_Q0C` scaled by the same factor that turns `corr_integral` into the Hardy--Littlewood
main term.
-/
noncomputable def q0ProjectedMainTermRaw (N : ℕ) : ℂ :=
  (((800 : ℝ) * (N : ℝ) : ℝ) : ℂ) * qa_mainTerm_Q0C N

/--
Step-24 extracted main term normalized to the raw bank σ-model scale.

This is the faithful normalization bridge from the arithmetic `q,a` extraction to the raw
`corr_integral`-scale σ-model before inserting the bank/window weight.
-/
noncomputable def q0ProjectedMainTermCorrModelRawNorm (N : ℕ) : ℂ :=
  ((((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even : ℝ)) : ℂ)
    * qa_mainTerm_Q0C N

/--
Step-24 extracted main term normalized all the way to the banked/windowed σ-model scale.

This is the deterministic endpoint aligned with the existing small-`β` theorem.
-/
noncomputable def q0ProjectedMainTermCorrModelNorm (X N : ℕ) : ℂ :=
  ((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ) * q0ProjectedMainTermCorrModelRawNorm N

lemma q0ProjectedMainTermRaw_eq_scale_sigmaTrunc (N : ℕ) :
    q0ProjectedMainTermRaw N
      = ((((800 : ℝ) * (N : ℝ)
            * Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N : ℝ)) : ℂ) := by
  rw [q0ProjectedMainTermRaw, qa_mainTerm_Q0C_eq_sigma_trunc_Q0]
  simp [mul_assoc, mul_left_comm, mul_comm]

lemma q0ProjectedMainTermCorrModelRawNorm_eq_corrModelRaw (N : ℕ) :
    q0ProjectedMainTermCorrModelRawNorm N
      = Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N := by
  simpa [q0ProjectedMainTermCorrModelRawNorm] using
    (Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw_eq_logSq_mul_massEven_mul_qa_mainTerm_Q0C
      (N := N)).symm

lemma q0ProjectedMainTermCorrModelNorm_eq_corrModel (X N : ℕ) :
    q0ProjectedMainTermCorrModelNorm X N
      = Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N := by
  calc
    q0ProjectedMainTermCorrModelNorm X N
        = ((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)
            * Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N := by
              simp [q0ProjectedMainTermCorrModelNorm, q0ProjectedMainTermCorrModelRawNorm_eq_corrModelRaw]
    _ = Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N := by
          simpa using
            (Goldbach.Cert.MajorArcModules.CorrModel.corrModel_eq_weightMass_mul_corrModelRaw
              (X := X) (N := N)).symm

/--
Exact normalization factor from the projected Hardy--Littlewood-scale raw Step-24 term to the
raw bank σ-model.
-/
lemma q0ProjectedMainTermCorrModelRawNorm_eq_factor_mul_q0ProjectedMainTermRaw
    (N : ℕ) :
    q0ProjectedMainTermCorrModelRawNorm N
      =
    ((((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even
          / ((800 : ℝ) * (N : ℝ)) : ℝ)) : ℂ)
      * q0ProjectedMainTermRaw N := by
  by_cases hN0 : N = 0
  · subst hN0
    simp [q0ProjectedMainTermCorrModelRawNorm, q0ProjectedMainTermRaw, qa_mainTerm_Q0C]
  · have hN : ((800 : ℝ) * (N : ℝ)) ≠ 0 := by
      positivity
    rw [q0ProjectedMainTermCorrModelRawNorm, q0ProjectedMainTermRaw]
    set A : ℝ := (Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even
    set B : ℝ := (800 : ℝ) * (N : ℝ)
    have hcoeff : ((A : ℂ)) = (((A / B : ℝ) : ℂ) * ((B : ℂ))) := by
      have hcoeffR : A = (A / B) * B := by
        field_simp [A, B, hN]
      exact_mod_cast hcoeffR
    calc
      ((A : ℂ) * qa_mainTerm_Q0C N)
          = ((((A / B : ℝ) : ℂ) * ((B : ℂ))) * qa_mainTerm_Q0C N) := by
              rw [hcoeff]
      _ = (((A / B : ℝ) : ℂ) * (((B : ℂ) * qa_mainTerm_Q0C N))) := by ring
      _ = ((((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even
              / ((800 : ℝ) * (N : ℝ)) : ℝ)) : ℂ)
            * q0ProjectedMainTermRaw N := by
              simp [A, B, q0ProjectedMainTermRaw]

/--
Exact normalization factor from the projected Hardy--Littlewood-scale raw Step-24 term to the
banked/windowed σ-model.
-/
lemma q0ProjectedMainTermCorrModelNorm_eq_factor_mul_q0ProjectedMainTermRaw
    (X N : ℕ) :
    q0ProjectedMainTermCorrModelNorm X N
      =
    ((((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even
          * Goldbach.AO_WeightMass.weight_mass X
          / ((800 : ℝ) * (N : ℝ)) : ℝ)) : ℂ)
      * q0ProjectedMainTermRaw N := by
  calc
    q0ProjectedMainTermCorrModelNorm X N
        =
      ((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)
        * q0ProjectedMainTermCorrModelRawNorm N := by
          simp [q0ProjectedMainTermCorrModelNorm]
    _ =
      ((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)
        * (((((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even
              / ((800 : ℝ) * (N : ℝ)) : ℝ)) : ℂ)
            * q0ProjectedMainTermRaw N) := by
              rw [q0ProjectedMainTermCorrModelRawNorm_eq_factor_mul_q0ProjectedMainTermRaw]
    _ =
      ((((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even
            * Goldbach.AO_WeightMass.weight_mass X
            / ((800 : ℝ) * (N : ℝ)) : ℝ)) : ℂ)
        * q0ProjectedMainTermRaw N := by
          by_cases hN0 : N = 0
          · subst hN0
            simp [q0ProjectedMainTermRaw]
          · have hN : ((800 : ℝ) * (N : ℝ)) ≠ 0 := by positivity
            set A : ℝ := (Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even
            set B : ℝ := (800 : ℝ) * (N : ℝ)
            set w : ℝ := Goldbach.AO_WeightMass.weight_mass X
            have hmul :
                ((w : ℂ) * (((A / B : ℝ) : ℂ)))
                  = ((((A * w / B : ℝ)) : ℂ)) := by
                    have hmulR : w * (A / B) = A * w / B := by
                      field_simp [A, B, w, hN]
                    exact_mod_cast hmulR
            calc
              ((w : ℂ) * ((((A / B : ℝ) : ℂ) * q0ProjectedMainTermRaw N)))
                  =
                (((w : ℂ) * (((A / B : ℝ) : ℂ))) * q0ProjectedMainTermRaw N) := by
                  ring
              _ =
                ((((A * w / B : ℝ)) : ℂ))
                    * q0ProjectedMainTermRaw N := by rw [hmul]
              _ =
                ((((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even
                      * Goldbach.AO_WeightMass.weight_mass X
                      / ((800 : ℝ) * (N : ℝ)) : ℝ)) : ℂ)
                    * q0ProjectedMainTermRaw N := by
                      simp [A, B, w, mul_assoc, mul_left_comm, mul_comm]

/--
First deterministic normalization bridge: Step-24 raw extracted main term to the unwindowed
σ-model raw term.
-/
lemma q0ProjectedMainTermRaw_sub_corrModelRaw_eq_scale_gap
    (N : ℕ) :
    q0ProjectedMainTermRaw N
      - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N
        =
    ((((800 : ℝ) * (N : ℝ)
          - (Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even) : ℝ) : ℂ)
      * qa_mainTerm_Q0C N := by
  calc
    q0ProjectedMainTermRaw N
        - Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw N
      =
    ((((800 : ℝ) * (N : ℝ) : ℝ)) : ℂ) * qa_mainTerm_Q0C N
      - ((((Real.log (N : ℝ)) ^ 2
            * Goldbach.AO_SigmaModel.Canon.mass_even : ℝ)) : ℂ) * qa_mainTerm_Q0C N := by
        rw [q0ProjectedMainTermRaw]
        rw [Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw_eq_logSq_mul_massEven_mul_qa_mainTerm_Q0C]
    _ =
    ((((800 : ℝ) * (N : ℝ)
          - (Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even) : ℝ) : ℂ)
      * qa_mainTerm_Q0C N := by
        calc
          ((((800 : ℝ) * (N : ℝ) : ℝ)) : ℂ) * qa_mainTerm_Q0C N
              - ((((Real.log (N : ℝ)) ^ 2
                    * Goldbach.AO_SigmaModel.Canon.mass_even : ℝ)) : ℂ) * qa_mainTerm_Q0C N
            =
          qa_mainTerm_Q0C N
              * (((((800 : ℝ) * (N : ℝ) : ℝ)) : ℂ)
                  - ((((Real.log (N : ℝ)) ^ 2
                        * Goldbach.AO_SigmaModel.Canon.mass_even : ℝ)) : ℂ)) := by
                ring
          _ =
            ((((800 : ℝ) * (N : ℝ)
                  - (Real.log (N : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even) : ℝ) : ℂ)
              * qa_mainTerm_Q0C N := by
                simp [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]

private lemma corrModelTrueRaw_eq_scale_sigmaTrue {N : ℕ} (hN : 1 < N) :
    Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N
      =
    ((((800 : ℝ) * (N : ℝ)
          * Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal
              Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal
              Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization
              N : ℝ)) : ℂ) := by
  have hσ :
      Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal
          Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal
          Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization
          N
        =
      Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal.sigma N := by
    simpa [Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal] using
      Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization.sigma_eq_euler_global
        (show 0 < N by exact lt_trans (by decide : 0 < 1) hN)
  have hlog_sq_ne : (Real.log (N : ℝ)) ^ 2 ≠ 0 := by
    have hlog_pos : 0 < Real.log (N : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hN)
    exact pow_ne_zero 2 (ne_of_gt hlog_pos)
  simp [Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw,
    Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue,
    Goldbach.BankPieces.Cert.TrueSingularSeries.mainTermGlobal,
    Goldbach.MainTerm.M, Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal,
    div_eq_mul_inv, hσ, hlog_sq_ne, mul_assoc, mul_left_comm, mul_comm]

/--
Tail-only comparison between the extracted Step-24 `Q0` projected main term and the honest true
raw model `corrModelTrueRaw`.
-/
theorem q0ProjectedMainTermRaw_sub_corrModelTrueRaw_le_of_tail_bound
    (Δσ : ℕ → ℝ)
    (htail :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
        ‖q0ProjectedMainTermRaw N
            - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖
          ≤ (800 : ℝ) * (N : ℝ) * Δσ N := by
  intro X N hX hN
  have hN_ge_X : X ≤ N := by
    have hI : N ∈ IccShift X Goldbach.Analytic.H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_pos : 0 < N := lt_of_lt_of_le (by decide : 0 < Goldbach.Analytic.X0) (le_trans hX hN_ge_X)
  have hN_one : 1 < N := by
    have htwo : 2 ≤ N := Goldbach.Analytic.two_le_of_window hX hN
    exact lt_of_lt_of_le (by decide : 1 < 2) htwo
  have hσ :
      |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
          - Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal
              Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal
              Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization
              N|
        ≤ Δσ N :=
    Goldbach.BankPieces.Cert.TrueSingularSeries.sigma_trunc_Q0_vs_singular_of_tail_bound_global
      (S := Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal)
      (R := Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization)
      (Δσ := Δσ) htail hX hN
  have hscale_nonneg : 0 ≤ (800 : ℝ) * (N : ℝ) := by positivity
  calc
    ‖q0ProjectedMainTermRaw N
        - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖
      =
    ‖((((800 : ℝ) * (N : ℝ)
          * (Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
              - Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal
                  Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal
                  Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization
                  N) : ℝ)) : ℂ)‖ := by
        rw [q0ProjectedMainTermRaw_eq_scale_sigmaTrunc]
        rw [corrModelTrueRaw_eq_scale_sigmaTrue hN_one]
        norm_num [sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = |(800 : ℝ) * (N : ℝ)
          * (Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
              - Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal
                  Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal
                  Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization
                  N)| := by
        simpa using
          (RCLike.norm_ofReal (K := ℂ)
            ((800 : ℝ) * (N : ℝ)
              * (Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
                  - Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal
                      Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal
                      Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization
                      N)))
    _ = (800 : ℝ) * (N : ℝ)
          * |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
              - Goldbach.BankPieces.Cert.TrueSingularSeries.sigmaGlobal
                  Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanSeriesGlobal
                  Goldbach.BankPieces.Cert.TrueSingularSeries.ramanujanEulerProductRealization
                  N| := by
        have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
        rw [abs_mul, abs_mul]
        simp [abs_of_nonneg (show 0 ≤ (800 : ℝ) by positivity), abs_of_nonneg hN_nonneg,
          mul_assoc, mul_left_comm, mul_comm]
    _ ≤ (800 : ℝ) * (N : ℝ) * Δσ N := by
        exact mul_le_mul_of_nonneg_left hσ (by positivity)

/--
Exact factorization of the legacy `corrModel` versus the honest extracted Step-24 raw main term.

This is the remaining small-`β` model seam once the deterministic theorem is retargeted away from
`corrModel`.
-/
lemma corrModel_sub_q0ProjectedMainTermRaw_eq_scale_gap
    (X N : ℕ) :
    Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N - q0ProjectedMainTermRaw N
      =
    ((((Real.log (N : ℝ)) ^ 2
          * Goldbach.AO_SigmaModel.Canon.mass_even
          * Goldbach.AO_WeightMass.weight_mass X
        - (800 : ℝ) * (N : ℝ)) : ℝ) : ℂ)
      * qa_mainTerm_Q0C N := by
  calc
    Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N - q0ProjectedMainTermRaw N
      =
    ((((Real.log (N : ℝ)) ^ 2
          * Goldbach.AO_SigmaModel.Canon.mass_even
          * Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ) * qa_mainTerm_Q0C N
      - ((((800 : ℝ) * (N : ℝ) : ℝ)) : ℂ) * qa_mainTerm_Q0C N := by
        rw [Goldbach.Cert.MajorArcModules.CorrModel.corrModel_eq_weightMass_mul_corrModelRaw]
        rw [Goldbach.Cert.MajorArcModules.CorrModel.corrModelRaw_eq_logSq_mul_massEven_mul_qa_mainTerm_Q0C]
        simp [q0ProjectedMainTermRaw, mul_assoc, mul_left_comm, mul_comm]
    _ =
    ((((Real.log (N : ℝ)) ^ 2
          * Goldbach.AO_SigmaModel.Canon.mass_even
          * Goldbach.AO_WeightMass.weight_mass X
        - (800 : ℝ) * (N : ℝ)) : ℝ) : ℂ)
      * qa_mainTerm_Q0C N := by
        calc
          ((((Real.log (N : ℝ)) ^ 2
                * Goldbach.AO_SigmaModel.Canon.mass_even
                * Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ) * qa_mainTerm_Q0C N
              - ((((800 : ℝ) * (N : ℝ) : ℝ)) : ℂ) * qa_mainTerm_Q0C N
            =
          ((((Real.log (N : ℝ)) ^ 2
                * Goldbach.AO_SigmaModel.Canon.mass_even
                * Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ)
              * qa_mainTerm_Q0C N
            - qa_mainTerm_Q0C N * ((((800 : ℝ) * (N : ℝ) : ℝ)) : ℂ) := by
              ring
          _ = qa_mainTerm_Q0C N *
                (((((Real.log (N : ℝ)) ^ 2
                    * Goldbach.AO_SigmaModel.Canon.mass_even
                    * Goldbach.AO_WeightMass.weight_mass X : ℝ)) : ℂ)
                  - ((((800 : ℝ) * (N : ℝ) : ℝ)) : ℂ)) := by
                ring
          _ =
            ((((Real.log (N : ℝ)) ^ 2
                  * Goldbach.AO_SigmaModel.Canon.mass_even
                  * Goldbach.AO_WeightMass.weight_mass X
                - (800 : ℝ) * (N : ℝ)) : ℝ) : ℂ)
              * qa_mainTerm_Q0C N := by
                simp [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]

/--
Coarse envelope for the `corrModel` versus extracted-main-term mismatch.

This isolates the remaining small-`β` seam in a purely scalar coefficient.
-/
theorem norm_corrModel_sub_q0ProjectedMainTermRaw_le_scale_gap
    (X N : ℕ) :
    ‖Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N - q0ProjectedMainTermRaw N‖
      ≤
    |(Real.log (N : ℝ)) ^ 2
        * Goldbach.AO_SigmaModel.Canon.mass_even
        * Goldbach.AO_WeightMass.weight_mass X
      - (800 : ℝ) * (N : ℝ)| *
      Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst := by
  rw [corrModel_sub_q0ProjectedMainTermRaw_eq_scale_gap]
  set r : ℝ :=
    (Real.log (N : ℝ)) ^ 2
      * Goldbach.AO_SigmaModel.Canon.mass_even
      * Goldbach.AO_WeightMass.weight_mass X
    - (800 : ℝ) * (N : ℝ)
  have hcoeff :
      ‖((r : ℝ) : ℂ)‖ = |r| := by
    simpa using (RCLike.norm_ofReal (K := ℂ) r)
  calc
    ‖((((Real.log (N : ℝ)) ^ 2
            * Goldbach.AO_SigmaModel.Canon.mass_even
            * Goldbach.AO_WeightMass.weight_mass X
          - (800 : ℝ) * (N : ℝ)) : ℝ) : ℂ)
        * qa_mainTerm_Q0C N‖
      =
    |(Real.log (N : ℝ)) ^ 2
        * Goldbach.AO_SigmaModel.Canon.mass_even
        * Goldbach.AO_WeightMass.weight_mass X
      - (800 : ℝ) * (N : ℝ)| * ‖qa_mainTerm_Q0C N‖ := by
        rw [show ((((Real.log (N : ℝ)) ^ 2
              * Goldbach.AO_SigmaModel.Canon.mass_even
              * Goldbach.AO_WeightMass.weight_mass X
            - (800 : ℝ) * (N : ℝ)) : ℝ) : ℂ) = ((r : ℝ) : ℂ) by
              simp [r]]
        rw [norm_mul, hcoeff]
    _ ≤
      |(Real.log (N : ℝ)) ^ 2
          * Goldbach.AO_SigmaModel.Canon.mass_even
          * Goldbach.AO_WeightMass.weight_mass X
        - (800 : ℝ) * (N : ℝ)| *
        Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact Goldbach.BankPieces.Cert.ProjectedConstGapBridge.norm_qa_mainTerm_Q0C_le_qaPhaseUpperConst N

/--
Reduce the true `Q0` major-arc deviation to two explicit pieces:

1. the analytic extraction error against the raw Step-24 projected main term, and
2. the truncation-to-true-series tail term.
-/
theorem norm_corr_integral_major_Q0_sub_corrModelTrueRaw_le_of_extracted_main_term
    (Δ : ℝ)
    (εmain εtail : ℕ → ℝ)
    (hMain :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N‖ ≤ εmain X)
    (hTail :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖q0ProjectedMainTermRaw N
              - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖
            ≤ εtail X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral_major_Q0 X N Δ
            - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖
          ≤ εmain X + εtail X := by
  intro X N hX hN
  have hsplit :
      corr_integral_major_Q0 X N Δ
        - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N
        =
      (corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N)
        + (q0ProjectedMainTermRaw N
            - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N) := by
    ring
  calc
    ‖corr_integral_major_Q0 X N Δ
        - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖
      =
    ‖(corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N)
        + (q0ProjectedMainTermRaw N
            - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N)‖ := by
        simpa using congrArg (fun z : ℂ => ‖z‖) hsplit
    _ ≤ ‖corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N‖
          + ‖q0ProjectedMainTermRaw N
              - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖ := by
        simpa using
          (norm_add_le
            (corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N)
            (q0ProjectedMainTermRaw N
              - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N))
    _ ≤ εmain X + εtail X := by
        exact add_le_add (hMain hX hN) (hTail hX hN)

/--
Reduce the extracted `Q0` major deviation to the usual small/large-`β` split, but with the true
Step-24 raw main term `q0ProjectedMainTermRaw` as the target.
-/
theorem norm_corr_integral_major_Q0_sub_q0ProjectedMainTermRaw_le_of_small_large
    {X N : ℕ} {Δ εs εl : ℝ}
    (hdecomp :
      corr_integral_major_Q0 X N Δ
        =
      corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ)
    (hs :
      ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N‖ ≤ εs)
    (hl :
      ‖corr_integral_major_Q0_large X N Δ‖ ≤ εl) :
    ‖corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N‖ ≤ εs + εl := by
  have hrewrite :
      corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N
        =
      (corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N)
        + corr_integral_major_Q0_large X N Δ := by
    calc
      corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N
          =
        (corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ)
          - q0ProjectedMainTermRaw N := by
            simpa [hdecomp]
      _ =
        (corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N)
          + corr_integral_major_Q0_large X N Δ := by
            ring
  have htri :
      ‖(corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N)
          + corr_integral_major_Q0_large X N Δ‖
        ≤ ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N‖
            + ‖corr_integral_major_Q0_large X N Δ‖ := by
    simpa using
      (norm_add_le
        (corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N)
        (corr_integral_major_Q0_large X N Δ))
  calc
    ‖corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N‖
        =
      ‖(corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N)
          + corr_integral_major_Q0_large X N Δ‖ := by
            simpa [hrewrite]
    _ ≤ ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N‖
          + ‖corr_integral_major_Q0_large X N Δ‖ := htri
    _ ≤ εs + εl := add_le_add hs hl

/--
Window-uniform version of the true extracted `Q0` major deviation split.
-/
theorem norm_corr_integral_major_Q0_sub_q0ProjectedMainTermRaw_le_of_small_large_on_window
    (Δ : ℝ)
    (εs εl : ℕ → ℝ)
    (hInt :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          IntervalIntegrable
            (βIntegrand X N Δ)
            MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hSmall :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N‖ ≤ εs X)
    (hLarge :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral_major_Q0_large X N Δ‖ ≤ εl X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N‖ ≤ εs X + εl X := by
  intro X N hX hN
  have hdecomp :
      corr_integral_major_Q0 X N Δ
        =
      corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ :=
    by
      exact corr_integral_major_Q0_eq_small_add_large (X := X) (N := N) (Δ := Δ) (hInt hX hN)
  exact norm_corr_integral_major_Q0_sub_q0ProjectedMainTermRaw_le_of_small_large
    (hdecomp := hdecomp)
    (hs := hSmall hX hN)
    (hl := hLarge hX hN)

/--
Triangle-inequality reduction from the legacy small-`β` target `corrModel` to the honest extracted
Step-24 raw main term `q0ProjectedMainTermRaw`.
-/
theorem norm_corr_integral_major_Q0_small_sub_q0ProjectedMainTermRaw_le_of_corrModel_gap
    {X N : ℕ} {Δ εs εm : ℝ}
    (hs :
      ‖corr_integral_major_Q0_small X N Δ
          - Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N‖ ≤ εs)
    (hm :
      ‖Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N - q0ProjectedMainTermRaw N‖ ≤ εm) :
    ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N‖ ≤ εs + εm := by
  have hdecomp :
      corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N
        =
      (corr_integral_major_Q0_small X N Δ
          - Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N)
        + (Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N
            - q0ProjectedMainTermRaw N) := by
    ring
  calc
    ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N‖
      =
    ‖(corr_integral_major_Q0_small X N Δ
          - Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N)
        + (Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N
            - q0ProjectedMainTermRaw N)‖ := by
        simpa using congrArg (fun z : ℂ => ‖z‖) hdecomp
    _ ≤ ‖corr_integral_major_Q0_small X N Δ
            - Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N‖
          + ‖Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N
              - q0ProjectedMainTermRaw N‖ := by
        simpa using
          (norm_add_le
            (corr_integral_major_Q0_small X N Δ
              - Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N)
            (Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N
              - q0ProjectedMainTermRaw N))
    _ ≤ εs + εm := add_le_add hs hm

/--
Window-uniform version of the previous reduction.
-/
theorem norm_corr_integral_major_Q0_small_sub_q0ProjectedMainTermRaw_le_of_corrModel_gap_on_window
    (Δ : ℝ)
    (εs εm : ℕ → ℝ)
    (hs :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral_major_Q0_small X N Δ
              - Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N‖ ≤ εs X)
    (hm :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N
              - q0ProjectedMainTermRaw N‖ ≤ εm X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N‖ ≤ εs X + εm X := by
  intro X N hX hN
  exact norm_corr_integral_major_Q0_small_sub_q0ProjectedMainTermRaw_le_of_corrModel_gap
    (hs := hs hX hN)
    (hm := hm hX hN)

/--
Canonical deterministic `ε₂`-small route, now retargeted from `corrModel` to the honest
Step-24 raw extracted main term.

This cleanly isolates the remaining small-`β` seam: a window bound for
`‖corrModel X N - q0ProjectedMainTermRaw N‖`.
-/
theorem norm_corr_integral_major_Q0_small_sub_q0ProjectedMainTermRaw_le_of_deterministic_small
    (εm : ℕ → ℝ)
    (hm :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N
              - q0ProjectedMainTermRaw N‖ ≤ εm X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral_major_Q0_small X N
            (1 : ℝ)
            - q0ProjectedMainTermRaw N‖
          ≤ Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert.εs + εm X := by
  have hsmall :
      Q0MajorSmallBound
        (1 : ℝ)
        Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert.εs :=
    Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert.smallBound_of_upperBound
      Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic.major_arc_small_beta_upperBound
  intro X N hX hN
  exact norm_corr_integral_major_Q0_small_sub_q0ProjectedMainTermRaw_le_of_corrModel_gap
    (hs := hsmall.bound hX hN)
    (hm := hm hX hN)

/--
The deterministic small-`β` theorem already applies to the correctly normalized Step-24 main term.

This is the draft-faithful interface: the arithmetic `q,a` extraction is normalized to the
banked/windowed σ-model, and the existing small-`β` theorem stays targeted at that endpoint.
-/
theorem norm_corr_integral_major_Q0_small_sub_q0ProjectedMainTermCorrModelNorm_le_of_deterministic_small :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral_major_Q0_small X N
            (1 : ℝ)
            - q0ProjectedMainTermCorrModelNorm X N‖
          ≤ Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert.εs := by
  have hsmall :
      Q0MajorSmallBound
        (1 : ℝ)
        Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert.εs :=
    Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert.smallBound_of_upperBound
      Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic.major_arc_small_beta_upperBound
  intro X N hX hN
  rw [q0ProjectedMainTermCorrModelNorm_eq_corrModel]
  exact hsmall.bound hX hN

/--
Full `Q0` major deviation against the correctly normalized Step-24 main term.

This is just the existing `corrModel` split theorem rewritten through the exact identity
`q0ProjectedMainTermCorrModelNorm = corrModel`.
-/
theorem norm_corr_integral_major_Q0_sub_q0ProjectedMainTermCorrModelNorm_le_of_small_large
    {X N : ℕ} {Δ εs εl : ℝ}
    (hdecomp :
      corr_integral_major_Q0 X N Δ
        =
      corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ)
    (hs :
      ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermCorrModelNorm X N‖ ≤ εs)
    (hl :
      ‖corr_integral_major_Q0_large X N Δ‖ ≤ εl) :
    ‖corr_integral_major_Q0 X N Δ - q0ProjectedMainTermCorrModelNorm X N‖ ≤ εs + εl := by
  rw [q0ProjectedMainTermCorrModelNorm_eq_corrModel] at hs ⊢
  exact norm_corr_integral_major_Q0_sub_corrModel_le_of_small_large
    (hdecomp := hdecomp) (hs := hs) (hl := hl)

/--
Window-uniform full `Q0` major deviation against the normalized Step-24 main term.

This is the faithful theorem surface for the smoothed major-arc comparison: small-`β` is compared
to the normalized/windowed model, while large-`β` remains a pure tail term.
-/
theorem norm_corr_integral_major_Q0_sub_q0ProjectedMainTermCorrModelNorm_le_of_small_large_on_window
    (Δ : ℝ)
    (εs εl : ℕ → ℝ)
    (hInt :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          IntervalIntegrable
            (βIntegrand X N Δ)
            MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hSmall :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermCorrModelNorm X N‖ ≤ εs X)
    (hLarge :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral_major_Q0_large X N Δ‖ ≤ εl X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral_major_Q0 X N Δ - q0ProjectedMainTermCorrModelNorm X N‖ ≤ εs X + εl X := by
  intro X N hX hN
  have hdecomp :
      corr_integral_major_Q0 X N Δ
        =
      corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ :=
    corr_integral_major_Q0_eq_small_add_large (X := X) (N := N) (Δ := Δ) (hInt hX hN)
  have hs :
      ‖corr_integral_major_Q0_small X N Δ
          - Goldbach.Cert.MajorArcModules.CorrModel.corrModel X N‖ ≤ εs X := by
    simpa [q0ProjectedMainTermCorrModelNorm_eq_corrModel] using hSmall hX hN
  have hl : ‖corr_integral_major_Q0_large X N Δ‖ ≤ εl X := hLarge hX hN
  rw [q0ProjectedMainTermCorrModelNorm_eq_corrModel]
  exact norm_corr_integral_major_Q0_sub_corrModel_le_of_small_large
    (hdecomp := hdecomp) (hs := hs) (hl := hl)

/--
Triangle-inequality reduction for the true projected model on the `corr_integral` scale.

This is the honest analogue of the old `corr_integral - corrModel` bookkeeping lemma, but with the
target replaced by `corrModelTrueRaw`.
-/
theorem norm_corr_integral_sub_corrModelTrueRaw_le_of_two_bounds
    {X N : ℕ} {Δ : ℝ} {ε₁ ε₂ : ℝ}
    (h₁ : ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁)
    (h₂ :
      ‖corr_integral_major_Q0 X N Δ
          - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖ ≤ ε₂) :
    ‖corr_integral X N
        - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖
      ≤ ε₁ + ε₂ := by
  have hdecomp :
      corr_integral X N
        - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N
        =
      (corr_integral X N - corr_integral_major_Q0 X N Δ)
        + (corr_integral_major_Q0 X N Δ
            - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N) := by
    ring
  have hnormEq :
      ‖corr_integral X N
          - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖
        =
      ‖(corr_integral X N - corr_integral_major_Q0 X N Δ)
          + (corr_integral_major_Q0 X N Δ
              - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N)‖ := by
    simpa using congrArg (fun z : ℂ => ‖z‖) hdecomp
  rw [hnormEq]
  refine le_trans ?_ (add_le_add h₁ h₂)
  simpa using
    (norm_add_le
      (corr_integral X N - corr_integral_major_Q0 X N Δ)
      (corr_integral_major_Q0 X N Δ
        - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N))

/--
Reduce the true projected `conv_ref` gap to the two natural `Q0` analytic obligations:

1. the non-`Q0` remainder `corr_integral - corr_integral_major_Q0`, and
2. the `Q0` major-arc deviation from the true projected model.
-/
theorem conv_ref_mainTerm_gap_of_q0_two_bounds
    (Δ : ℝ)
    (ε₁ ε₂ : ℕ → ℝ)
    (h₁ :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁ X)
    (h₂ :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral_major_Q0 X N Δ
            - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖ ≤ ε₂ X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
      |Goldbach.BG_Identity.conv_ref X N - Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N|
        ≤ (1 / 135200 : ℝ) * (ε₁ X + ε₂ X) := by
  refine
    Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.conv_ref_mainTerm_gap_of_corr_integral_true_bound
      (ε := fun X => ε₁ X + ε₂ X) ?_
  intro X N hX hN
  exact norm_corr_integral_sub_corrModelTrueRaw_le_of_two_bounds
    (h₁ := h₁ hX hN)
    (h₂ := h₂ hX hN)

/--
Bank-gap reduction for the true projected model from the two natural `Q0` analytic obligations.
-/
theorem bank_gap_of_q0_two_bounds
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δ : ℝ)
    (ε₁ ε₂ Δproj : ℕ → ℝ)
    (h₁ :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁ X)
    (h₂ :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
        ‖corr_integral_major_Q0 X N Δ
            - Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.corrModelTrueRaw N‖ ≤ ε₂ X)
    (hCal :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
        Goldbach.AO_WeightMass.weight_mass X
          * (Goldbach.BG_Bank.payload_cap X N
              * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
          + (1 / 135200 : ℝ) * (ε₁ X + ε₂ X)
          ≤ Δproj X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
      |Goldbach.BG_Identity.R_bank X N - Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N|
        ≤ Δproj X := by
  refine
    Goldbach.BankPieces.Cert.ProjectedTrueFromCorrIntegral.bank_gap_of_corr_integral_true_bound
      (ε := fun X => ε₁ X + ε₂ X)
      (Δproj := Δproj)
      ?_ hCal
  intro X N hX hN
  exact norm_corr_integral_sub_corrModelTrueRaw_le_of_two_bounds
    (h₁ := h₁ hX hN)
    (h₂ := h₂ hX hN)

/--
Full true projected `Q0` route from the extracted Step-24 main term.

This is the clean theorem surface mined from Step 24/26:

1. minor/complement bound,
2. `Q0`-major-arc bound against the extracted raw `q/a` main term,
3. explicit tail bound from `sigma_trunc_Q0` to the true singular series.
-/
theorem bank_gap_of_q0_extracted_main_term
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δ : ℝ)
    (ε₁ εmain εtail Δσ Δproj : ℕ → ℝ)
    (hMinor :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁ X)
    (hMain :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral_major_Q0 X N Δ - q0ProjectedMainTermRaw N‖ ≤ εmain X)
    (htail :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N)
    (hTailEnv :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          (800 : ℝ) * (N : ℝ) * Δσ N ≤ εtail X)
    (hCal :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
            + (1 / 135200 : ℝ) * (ε₁ X + (εmain X + εtail X))
            ≤ Δproj X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N|
          ≤ Δproj X := by
  refine bank_gap_of_q0_two_bounds (Δ := Δ)
    (ε₁ := ε₁) (ε₂ := fun X => εmain X + εtail X) (Δproj := Δproj)
    hMinor ?_ hCal
  intro X N hX hN
  refine norm_corr_integral_major_Q0_sub_corrModelTrueRaw_le_of_extracted_main_term
    (Δ := Δ) (εmain := εmain) (εtail := εtail) (hMain := hMain) ?_ hX hN
  intro X N hX hN
  have hraw :=
    q0ProjectedMainTermRaw_sub_corrModelTrueRaw_le_of_tail_bound
      (Δσ := Δσ) (htail := htail) hX hN
  exact le_trans hraw (hTailEnv hX hN)

/--
True projected `Q0` route via the old small/large-`β` split, but still targeting the honest
extracted Step-24 main term.
-/
theorem bank_gap_of_q0_split_extracted_main_term
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (Δ : ℝ)
    (ε₁ εs εl εtail Δσ Δproj : ℕ → ℝ)
    (hInt :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          IntervalIntegrable
            (βIntegrand X N Δ)
            MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hMinor :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁ X)
    (hSmall :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral_major_Q0_small X N Δ - q0ProjectedMainTermRaw N‖ ≤ εs X)
    (hLarge :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          ‖corr_integral_major_Q0_large X N Δ‖ ≤ εl X)
    (htail :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          |Goldbach.AO_OffDiag.SigmaTailReindex.sigmaTail N| ≤ Δσ N)
    (hTailEnv :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          (800 : ℝ) * (N : ℝ) * Δσ N ≤ εtail X)
    (hCal :
      ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
        N ∈ EvenIn X Goldbach.Analytic.H →
          Goldbach.AO_WeightMass.weight_mass X
            * (Goldbach.BG_Bank.payload_cap X N
                * (((3 : ℝ) / 1000) + Goldbach.BG_Identity.C_tail_closed))
            + (1 / 135200 : ℝ) * (ε₁ X + ((εs X + εl X) + εtail X))
            ≤ Δproj X) :
    ∀ {X N : ℕ}, Goldbach.Analytic.X0 ≤ X →
      N ∈ EvenIn X Goldbach.Analytic.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BankPieces.Cert.ProjectedTrueInput.Mtrue N|
          ≤ Δproj X := by
  refine bank_gap_of_q0_extracted_main_term
    (Δ := Δ) (ε₁ := ε₁) (εmain := fun X => εs X + εl X)
    (εtail := εtail) (Δσ := Δσ) (Δproj := Δproj)
    hMinor ?_ htail hTailEnv hCal
  intro X N hX hN
  exact norm_corr_integral_major_Q0_sub_q0ProjectedMainTermRaw_le_of_small_large_on_window
    (Δ := Δ) (εs := εs) (εl := εl) hInt hSmall hLarge hX hN

end

end Goldbach.BankPieces.Cert.ProjectedTrueFromQ0
