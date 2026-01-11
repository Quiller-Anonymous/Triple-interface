import Goldbach.Cert.MajorArcStep17MajorMinorSplit
import Goldbach.Cert.MajorArcStep22BetaKernelLocalization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Major arcs (Step 25, sigma-agnostic): minor-arc bound scaffolding.

This file does **not** prove a genuine minor-arc estimate (which would require cancellation).
Instead, it packages clean “plumbing” lemmas reducing the minor-arc contribution to pointwise
bounds on the shifted exponential sums on the minor arcs.
-/

namespace Goldbach.Cert
namespace MajorArcStep25MinorArcBound

open scoped Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep15Parameters
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep22BetaKernelLocalization

noncomputable section

-- Match the `UC` used throughout the major-arc integral pipeline.
abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

-- The universal (project-fixed) kernel cap coming from the tent kernel normalization.
noncomputable def kernelCap : ℝ :=
  ((2 * Goldbach.BankParams.H + 1 : ℝ) / (Goldbach.BG_Identity.Ucut : ℝ))

lemma kernelCap_nonneg : 0 ≤ kernelCap := by
  have hU : 0 < (Goldbach.BG_Identity.Ucut : ℝ) := Goldbach.BG_Identity.Ucut_pos_real
  have hnum : 0 ≤ (2 * Goldbach.BankParams.H + 1 : ℝ) := by
    have : (0 : ℕ) ≤ 2 * Goldbach.BankParams.H + 1 := Nat.zero_le _
    exact_mod_cast this
  exact div_nonneg hnum (le_of_lt hU)

lemma norm_kernelPolyC_le_kernelCap (x : UC) :
    ‖kernelPolyC x‖ ≤ kernelCap := by
  have h1 :=
    Goldbach.Cert.MajorArcStep22BetaKernelLocalization.norm_kernelPolyC_le_sum_abs_K_full (x := x)
  have h2 := Goldbach.BG_Identity.sum_abs_K_full_inner_le
  exact le_trans h1 (by simpa [kernelCap] using h2)

/-- The α-integral appearing in the definition of `corr_integral_minor` (Step 17). -/
noncomputable def innerMinor (X N : ℕ) (B : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ),
    (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α

lemma corr_integral_minor_eq (X N : ℕ) (B : ℕ) (Δ : ℝ) :
    corr_integral_minor X N B Δ
      =
    ∫ β in (0 : ℝ)..(1 : ℝ), kernelPolyC (β : UC) * innerMinor X N B Δ β := by
  rfl

/--
If both shifted exponential sums are uniformly bounded by `M` on the **minor arcs**, then the
corresponding α-integral is bounded by `M^2`.

This is a purely formal reduction: it avoids any genuine minor-arc cancellation.
-/
theorem norm_innerMinor_le_sq_of_expSum_bound
    (X N : ℕ) (B : ℕ) (Δ : ℝ) (M : ℝ) (hM : 0 ≤ M) (β : ℝ)
    (hsub : ∀ {α : ℝ}, α ∈ (majorArcSetTextbook X B Δ)ᶜ →
      ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M)
    (hadd : ∀ {α : ℝ}, α ∈ (majorArcSetTextbook X B Δ)ᶜ →
      ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M) :
    ‖innerMinor X N B Δ β‖ ≤ M ^ 2 := by
  -- Use the constant bound on the integrand over the interval.
  have hconst :
      ∀ α ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖(majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α‖ ≤ M ^ 2 := by
    intro α _hαI
    by_cases hα : α ∈ (majorArcSetTextbook X B Δ)ᶜ
    · -- On the minor arcs: use the assumed bounds on `expSum(α±β)`.
      have hI :
          ‖innerIntegrand X N β α‖ ≤ M ^ 2 := by
        -- `innerIntegrand = fourier(-N) * expSum(α-β) * expSum(α+β)` and `‖fourier‖=1`.
        have hfour : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ = 1 := by
          simp [fourier_apply]
        have hmul :
            ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M ^ 2 := by
          have h1 : ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M := hsub (α := α) hα
          have h2 : ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M := hadd (α := α) hα
          have : ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M * M :=
            mul_le_mul h1 h2 (norm_nonneg _) hM
          simpa [pow_two] using this

        -- Now bound the integrand norm.
        calc
          ‖innerIntegrand X N β α‖
              = ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                    * expSum X N ((α : UC) - (β : UC))
                    * expSum X N ((α : UC) + (β : UC))‖ := by
                    rfl
          _ = ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
                * ‖expSum X N ((α : UC) - (β : UC))‖
                * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                simp [mul_assoc]
          _ = 1 * ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                -- `‖fourier‖ = 1`
                rw [hfour]
          _ = ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                simp
          _ ≤ M ^ 2 := hmul
      -- Indicators: on the set, the indicator is the function itself.
      simpa [Set.indicator_of_mem hα] using hI
    · -- Off the minor arcs, the indicator is zero.
      have h0 : (0 : ℝ) ≤ M ^ 2 := by nlinarith [sq_nonneg M]
      have h0' : ‖(0 : ℂ)‖ ≤ M ^ 2 := by simpa using h0
      simpa [Set.indicator_of_notMem hα] using h0'

  -- Apply the interval-integral bound by a constant (interval length is `1`).
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := M ^ 2)
      (f := fun α : ℝ =>
        (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)
      hconst
  simpa [innerMinor] using h

/--
Minor-arc bound reduction: if the shifted exponential sums are uniformly bounded by `M` on the
minor arcs, then `‖corr_integral_minor‖ ≤ kernelCap * M^2`.

This is the natural “interface” needed once a genuine minor-arc estimate is available.
-/
theorem norm_corr_integral_minor_le_kernelCap_mul_sq_of_expSum_bound
    (X N : ℕ) (B : ℕ) (Δ : ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hsub : ∀ {β α : ℝ}, α ∈ (majorArcSetTextbook X B Δ)ᶜ →
      ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M)
    (hadd : ∀ {β α : ℝ}, α ∈ (majorArcSetTextbook X B Δ)ᶜ →
      ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M) :
    ‖corr_integral_minor X N B Δ‖ ≤ kernelCap * (M ^ 2) := by
  -- Bound the outer integrand pointwise by `kernelCap * M^2`.
  have houter :
      ∀ β ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖kernelPolyC (β : UC) * innerMinor X N B Δ β‖ ≤ kernelCap * (M ^ 2) := by
    intro β _hβI
    have hK : ‖kernelPolyC (β : UC)‖ ≤ kernelCap :=
      norm_kernelPolyC_le_kernelCap (x := (β : UC))
    have hI : ‖innerMinor X N B Δ β‖ ≤ M ^ 2 :=
      norm_innerMinor_le_sq_of_expSum_bound (X := X) (N := N) (B := B) (Δ := Δ) (M := M) (hM := hM)
        (β := β) (hsub := fun {α} hα => hsub (β := β) (α := α) hα)
        (hadd := fun {α} hα => hadd (β := β) (α := α) hα)
    calc
      ‖kernelPolyC (β : UC) * innerMinor X N B Δ β‖
          = ‖kernelPolyC (β : UC)‖ * ‖innerMinor X N B Δ β‖ := by
              simp
      _ ≤ kernelCap * (M ^ 2) := by
              exact mul_le_mul hK hI (norm_nonneg _) (kernelCap_nonneg)

  -- Integrate the constant bound over `[0,1]`.
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := kernelCap * (M ^ 2))
      (f := fun β : ℝ => kernelPolyC (β : UC) * innerMinor X N B Δ β)
      houter
  simpa [corr_integral_minor_eq] using h

end

end MajorArcStep25MinorArcBound
end Goldbach.Cert
