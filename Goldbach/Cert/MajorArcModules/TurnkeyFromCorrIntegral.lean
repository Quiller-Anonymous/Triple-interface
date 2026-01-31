import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Cert.MajorArcModules.CorrModel
import Goldbach.Cert.MajorArcModules.Normalization
import Goldbach.Cert.MajorArcModules.NumericFacts
import Goldbach.Cert.MajorArcModules.TurnkeyCanon

/-!
`MajorArcModules/TurnkeyFromCorrIntegral` is an intermediate reduction step for the turnkey
certificate route.

It isolates the purely algebraic/log-normalization part of the final goal:

*If* one can bound the complex correlation integral `corr_integral X N` against its expected model
value (scaled by `(log N)^2`), then one gets the pipeline-facing real bound
`|RΛ_smooth X N - RΛ_model X N| ≤ δ_major_canon` on the canonical window.

This file does **not** attempt to prove the hard analytic bound on `corr_integral`; it is the
bridge that lets the future certificate focus on bounding a single complex quantity.
-/

namespace Goldbach.Cert.MajorArcModules.TurnkeyFromCorrIntegral

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcAxiomsFunX
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.Normalization
open Goldbach.Cert.MajorArcModules.NumericFacts
open Goldbach.Cert.MajorArcModules.TurnkeyCanon

noncomputable section

private lemma X_le_of_mem_IccShift {X H N : ℕ} (hN : N ∈ Goldbach.Windows.IccShift X H) : X ≤ N := by
  classical
  -- `IccShift X H = (range (H+1)).image (fun k => X + k)`.
  rcases Finset.mem_image.mp hN with ⟨k, hk, rfl⟩
  exact Nat.le_add_right X k

private lemma X0_le_of_mem_EvenIn {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) : X0 ≤ N := by
  classical
  have hIn : N ∈ Goldbach.Windows.IccShift X H := (Finset.mem_filter.mp hN).1
  exact le_trans hX (X_le_of_mem_IccShift (X := X) (H := H) (N := N) hIn)

/-- The global normalization factor appearing in `RΛ_smooth_cast_eq_norm_mul_corr_integral`. -/
private noncomputable def normFactor (N : ℕ) : ℝ :=
  (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)

private lemma normFactor_nonneg (N : ℕ) : 0 ≤ normFactor N := by
  have : 0 ≤ (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) := by
    exact one_div_nonneg.mpr (sq_nonneg _)
  have : 0 ≤ (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2) :=
    mul_nonneg (by norm_num) this
  simpa [normFactor] using this

private lemma norm_normFactor_le (N : ℕ) (hN : X0 ≤ N) :
    ‖(normFactor N : ℂ)‖ ≤ (1 / 135200 : ℝ) := by
  have hlog : (13 : ℝ) ≤ Real.log (N : ℝ) := thirteen_le_log_of_X0_le (X := N) hN
  have hsq : (169 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by
    -- Square the lower bound `13 ≤ log N` using monotonicity of multiplication on `ℝ_{≥0}`.
    have hlog0 : 0 ≤ Real.log (N : ℝ) := le_trans (by norm_num) hlog
    have hmul :
        (13 : ℝ) * (13 : ℝ) ≤ (Real.log (N : ℝ)) * (Real.log (N : ℝ)) :=
      mul_le_mul hlog hlog (by norm_num) hlog0
    have h13 : (13 : ℝ) * (13 : ℝ) = (169 : ℝ) := by norm_num
    simpa [pow_two, h13] using hmul
  have hone_div : (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) ≤ (1 / 169 : ℝ) := by
    -- Larger denominator gives smaller `1/·`.
    have hpos : (0 : ℝ) < (169 : ℝ) := by norm_num
    simpa using (one_div_le_one_div_of_le hpos hsq)
  have hnf_le : normFactor N ≤ (1 / 135200 : ℝ) := by
    -- `normFactor N = (1/800) * (1/(log N)^2) ≤ (1/800) * (1/169) = 1/135200`.
    have h' :
        normFactor N ≤ (1 / 800 : ℝ) * (1 / 169 : ℝ) := by
      have : (1 / (Real.log (N : ℝ)) ^ 2 : ℝ) ≤ (1 / 169 : ℝ) := hone_div
      -- multiply by `1/800` on the left (nonnegative)
      have hmul :
          (1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)
            ≤
          (1 / 800 : ℝ) * (1 / 169 : ℝ) :=
        mul_le_mul_of_nonneg_left this (by norm_num)
      simpa [normFactor] using hmul
    have hconst : (1 / 800 : ℝ) * (1 / 169 : ℝ) = (1 / 135200 : ℝ) := by norm_num
    exact le_trans h' (le_of_eq hconst)
  -- Convert the real bound into a bound on the complex norm (of a real).
  have hnf0 : 0 ≤ normFactor N := normFactor_nonneg N
  have hnorm : ‖(normFactor N : ℂ)‖ = normFactor N := by
    -- `‖(r : ℂ)‖ = |r| = r` for `r ≥ 0`.
    have habs : ‖(normFactor N : ℂ)‖ = |normFactor N| := by
      calc
        ‖(normFactor N : ℂ)‖ = ‖normFactor N‖ := by simpa using (Complex.norm_real (normFactor N))
        _ = |normFactor N| := Real.norm_eq_abs _
    simpa [abs_of_nonneg hnf0] using habs
  -- Avoid `simp` rewriting `‖↑r‖` into `|r|` on the goal.
  rw [hnorm]
  exact hnf_le

private lemma normFactor_mul_corrModel_eq_sigma_mass (X N : ℕ) (hN : X0 ≤ N) :
    (normFactor N : ℂ) * corrModel X N =
      (Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X : ℂ) := by
  have hlog : (13 : ℝ) ≤ Real.log (N : ℝ) := thirteen_le_log_of_X0_le (X := N) hN
  have hlog_ne : Real.log (N : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 13) hlog)
  have hpow_ne : (Real.log (N : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
  -- Prove the corresponding identity in `ℝ`, then cast to `ℂ`.
  have hReal :
      normFactor N * ((Real.log (N : ℝ)) ^ 2 * (800 : ℝ)
          * Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X)
        =
      Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X := by
    set L : ℝ := (Real.log (N : ℝ)) ^ 2
    have hL : L ≠ 0 := by simpa [L] using hpow_ne
    -- Unfold `normFactor`, rewrite everything in terms of `L`, and let `simp` cancel.
    -- The only nontrivial cancellation is `(1/L) * L = 1`, which uses `hL`.
    -- The `mul_assoc` hints are only for reassociation, not for rewriting numerics.
    have :
        (1 / 800 : ℝ) *
            ((1 / L : ℝ) *
              (L * ((800 : ℝ) * Goldbach.AO_SigmaModel.sigma N)
                * Goldbach.AO_WeightMass.weight_mass X))
          =
        Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X := by
      simp [one_div, hL, mul_assoc, mul_left_comm, mul_comm]
    -- Now match the displayed expression with the original one.
    simpa [normFactor, L, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using this
  -- Cast the real identity into `ℂ` and rewrite the LHS to match `corrModel`.
  have hC :
      ((normFactor N
          * ((Real.log (N : ℝ)) ^ 2 * (800 : ℝ)
              * Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X)) : ℂ)
        =
      (Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X : ℂ) := by
    simpa using congrArg (fun r : ℝ => (r : ℂ)) hReal
  simpa [corrModel, mul_assoc, mul_left_comm, mul_comm] using hC

/--
Turn a bound on the complex correlation integral into the canonical major-arc on-window bound.

The hypothesis `hCorr` is the *hard* analytic input; the rest is pure normalization and triangle
inequality bookkeeping. The “log interaction” is limited to the fixed inequality
`13 ≤ log N` on the canonical window, via `MajorArcNumericFacts`.
-/
theorem turnkey_of_corr_integral_bound
    (ε : ℝ)
    (hCorr :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → ‖corr_integral X N - corrModel X N‖ ≤ ε)
    (hε :
      (1 / 135200 : ℝ) * ε ≤ δ_major_canon) :
    TurnkeyMajorArcCanon := by
  refine ⟨?_⟩
  intro X N hX hN
  have hN0 : X0 ≤ N := X0_le_of_mem_EvenIn (X := X) (N := N) hX hN
  have hCorr' : ‖corr_integral X N - corrModel X N‖ ≤ ε := hCorr hX hN

  -- Work in `ℂ` and then switch back to `ℝ` at the end.
  have hsmoothC :
      (RΛ_smooth X N : ℂ) = (normFactor N : ℂ) * corr_integral X N := by
    simpa [normFactor, mul_assoc, mul_left_comm, mul_comm] using
      (RΛ_smooth_cast_eq_norm_mul_corr_integral (X := X) (N := N))
  have hmodelC :
      (RΛ_model X N : ℂ) =
        (Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X : ℂ) := by
    simp [RΛ_model_eq_sigma_mul_weight_mass]

  have hdiffC :
      (RΛ_smooth X N : ℂ) - (RΛ_model X N : ℂ)
        =
      (normFactor N : ℂ) * (corr_integral X N - corrModel X N) := by
    -- Substitute the two identities and factor out `normFactor`.
    rw [hsmoothC, hmodelC]
    have hmain :
        (normFactor N : ℂ) * corrModel X N =
          (Goldbach.AO_SigmaModel.sigma N * Goldbach.AO_WeightMass.weight_mass X : ℂ) :=
      normFactor_mul_corrModel_eq_sigma_mass (X := X) (N := N) hN0
    -- `nf*corr - sigma = nf*corr - nf*corrModel = nf*(corr - corrModel)`.
    simp [hmain, mul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, mul_assoc]

  have hnormC :
      ‖(RΛ_smooth X N : ℂ) - (RΛ_model X N : ℂ)‖
        ≤
      (1 / 135200 : ℝ) * ε := by
    have hnf_abs : ‖(normFactor N : ℂ)‖ = |normFactor N| := by
      calc
        ‖(normFactor N : ℂ)‖ = ‖normFactor N‖ := by
          simpa using (Complex.norm_real (normFactor N))
        _ = |normFactor N| := Real.norm_eq_abs _
    have hnf_abs_le : |normFactor N| ≤ (1 / 135200 : ℝ) := by
      -- Rewrite the bound on the complex norm into a bound on the real absolute value.
      simpa [hnf_abs] using (norm_normFactor_le (N := N) hN0)
    calc
      ‖(RΛ_smooth X N : ℂ) - (RΛ_model X N : ℂ)‖
          = ‖(normFactor N : ℂ) * (corr_integral X N - corrModel X N)‖ := by
              simpa using congrArg (fun z : ℂ => ‖z‖) hdiffC
      _ = |normFactor N| * ‖corr_integral X N - corrModel X N‖ := by
              -- `‖(r:ℂ)‖ = |r|` for `r : ℝ`.
              simpa [hnf_abs] using
                (norm_mul (normFactor N : ℂ) (corr_integral X N - corrModel X N))
      _ ≤ (1 / 135200 : ℝ) * ‖corr_integral X N - corrModel X N‖ := by
              exact mul_le_mul_of_nonneg_right hnf_abs_le (norm_nonneg _)
      _ ≤ (1 / 135200 : ℝ) * ε := by
              exact mul_le_mul_of_nonneg_left hCorr' (by norm_num)

  -- Convert the complex-norm bound back to a real absolute value.
  have habs :
      |RΛ_smooth X N - RΛ_model X N|
        =
      ‖(RΛ_smooth X N : ℂ) - (RΛ_model X N : ℂ)‖ := by
    -- Both sides are reals, so the complex norm is the real norm, hence `Real.abs`.
    set x : ℝ := RΛ_smooth X N - RΛ_model X N
    have hx : (x : ℂ) = (RΛ_smooth X N : ℂ) - (RΛ_model X N : ℂ) := by
      simp [x]
    calc
      |RΛ_smooth X N - RΛ_model X N|
          = |x| := by simp [x]
      _ = ‖x‖ := (Real.norm_eq_abs x).symm
      _ = ‖(x : ℂ)‖ := by
            simpa using (Complex.norm_real x).symm
      _ = ‖(RΛ_smooth X N : ℂ) - (RΛ_model X N : ℂ)‖ := by
            simpa [hx]
  -- Finish using the supplied rational-friendly inequality `hε`.
  have : |RΛ_smooth X N - RΛ_model X N| ≤ (1 / 135200 : ℝ) * ε := by
    simpa [habs] using hnormC
  exact le_trans this hε

end

end Goldbach.Cert.MajorArcModules.TurnkeyFromCorrIntegral
