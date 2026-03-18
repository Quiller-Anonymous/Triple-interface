import Mathlib
import Goldbach.Cert.MajorArcModules.MainTermQ0
import Goldbach.MainTerm
import Goldbach.Analytic.NumericSigma
import Goldbach.Cert.CanonLogBounds
import Goldbach.Windows

namespace Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge

open Goldbach
open Goldbach.Windows
open Goldbach.Analytic
open Goldbach.Cert.MajorArcModules.MainTermQ0
open Complex
open Real

noncomputable section

variable (C : Goldbach.Singular.C2Const)

/--
The correctly scaled Step-24 truncation object for comparison with the projected Hardy--Littlewood
main term.

Unlike `sigmaHonestWeighted`, this is on the same `N / log^2 N` scale as `MainTerm.M`.
-/
noncomputable def sigmaTruncProjected (N : ℕ) : ℝ :=
  Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N * ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)

/--
Complex Step-24 version of `sigmaTruncProjected`, expressed via the extracted q/a main term.
-/
noncomputable def qaProjectedMainTermC (N : ℕ) : ℂ :=
  (((N : ℝ) / (Real.log (N : ℝ)) ^ 2 : ℝ) : ℂ) * qa_mainTerm_Q0C N

lemma qaProjectedMainTermC_eq_sigmaTruncProjected (N : ℕ) :
    qaProjectedMainTermC N = (((sigmaTruncProjected N : ℝ) : ℂ)) := by
  rw [qaProjectedMainTermC, qa_mainTerm_Q0C_eq_sigma_trunc_Q0]
  simp [sigmaTruncProjected, mul_assoc, mul_left_comm, mul_comm]

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

/--
Exact reduction of the scaled projected seam to a comparison between the truncated singular-series
object `sigma_trunc_Q0` and the classical Hardy--Littlewood singular series.
-/
theorem sigmaTruncProjected_mainTerm_gap_of_sigmaGap
    (Δσ : ℕ → ℝ)
    (hσ :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
            - Goldbach.Singular.sigma C N| ≤ Δσ N) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |sigmaTruncProjected N - (Goldbach.MainTerm.M C) N|
        ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Δσ N := by
  intro X N hX hN
  have hscale_nonneg :
      0 ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
    scale_nonneg_of_window hX hN
  have hσN :
      |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
          - Goldbach.Singular.sigma C N| ≤ Δσ N :=
    hσ (X := X) (N := N) hX hN
  calc
    |sigmaTruncProjected N - (Goldbach.MainTerm.M C) N|
        = |((N : ℝ) / (Real.log (N : ℝ)) ^ 2)
            * (Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
                - Goldbach.Singular.sigma C N)| := by
            have hsplit :
                sigmaTruncProjected N - (Goldbach.MainTerm.M C) N
                  = ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)
                      * (Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
                          - Goldbach.Singular.sigma C N) := by
                  simp [sigmaTruncProjected, Goldbach.MainTerm.M, div_eq_mul_inv]
                  ring
            rw [hsplit]
    _ = ((N : ℝ) / (Real.log (N : ℝ)) ^ 2)
          * |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
              - Goldbach.Singular.sigma C N| := by
            rw [abs_mul, abs_of_nonneg hscale_nonneg]
    _ ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Δσ N := by
          exact mul_le_mul_of_nonneg_left hσN hscale_nonneg

/--
Complex q/a-shaped version of `sigmaTruncProjected_mainTerm_gap_of_sigmaGap`.
-/
theorem qaProjectedMainTermC_mainTerm_gap_of_sigmaGap
    (Δσ : ℕ → ℝ)
    (hσ :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        |Goldbach.AO_OffDiag.TailBlock.sigma_trunc_Q0 N
            - Goldbach.Singular.sigma C N| ≤ Δσ N) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      ‖qaProjectedMainTermC N - ((((Goldbach.MainTerm.M C) N : ℝ) : ℂ))‖
        ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Δσ N := by
  intro X N hX hN
  have hreal :
      |sigmaTruncProjected N - (Goldbach.MainTerm.M C) N|
        ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Δσ N :=
    sigmaTruncProjected_mainTerm_gap_of_sigmaGap (C := C) (Δσ := Δσ) (hσ := hσ) (X := X) (N := N) hX hN
  have hcast :
      ‖((((sigmaTruncProjected N - (Goldbach.MainTerm.M C) N : ℝ)) : ℂ))‖
        = |sigmaTruncProjected N - (Goldbach.MainTerm.M C) N| := by
    simpa using
      (RCLike.norm_ofReal (K := ℂ) (sigmaTruncProjected N - (Goldbach.MainTerm.M C) N))
  calc
    ‖qaProjectedMainTermC N - ((((Goldbach.MainTerm.M C) N : ℝ) : ℂ))‖
        = ‖((((sigmaTruncProjected N - (Goldbach.MainTerm.M C) N : ℝ)) : ℂ))‖ := by
            rw [qaProjectedMainTermC_eq_sigmaTruncProjected]
            simp
    _ = |sigmaTruncProjected N - (Goldbach.MainTerm.M C) N| := hcast
    _ ≤ ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) * Δσ N := hreal

end

end Goldbach.BankPieces.Cert.ProjectedScaledMainTermBridge
