import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
import Goldbach.Cert.MajorArcStep25MinorArcBound
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
`MajorArcModules/MinorQ0Bound` provides a Step-25-style *reduction* for the `Q0`-complement piece
`corr_integral_minor_Q0` (defined in `MajorArcModules/CorrIntegralQ0Reduction`).

It does **not** prove a genuine minor-arc estimate (which would require cancellation).  Instead,
it shows:

if the shifted exponential sums are uniformly bounded by `M` on `((majorArcSetQ0 X Δ)ᶜ)`, then
`‖corr_integral_minor_Q0 X N Δ‖ ≤ kernelCap * M^2`.

This file also provides an `L²`-based variant of the reduction:

if one has **restricted** `L²` energy bounds for the shifted exponential sums on
`((majorArcSetQ0 X Δ)ᶜ)`, then
`‖corr_integral_minor_Q0 X N Δ‖ ≤ kernelCap * M2`.

This is part of the offline/turnkey “MajorArcModules” staging area.
-/

namespace Goldbach.Cert.MajorArcModules.MinorQ0Bound

open scoped Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral

noncomputable section

-- Match the `UC` used throughout the major-arc integral pipeline.
abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

-- Reuse the Step-25 kernel cap (which is purely project-defined, not analytic).
noncomputable abbrev kernelCap : ℝ := Goldbach.Cert.MajorArcStep25MinorArcBound.kernelCap

lemma kernelCap_nonneg : 0 ≤ kernelCap :=
  Goldbach.Cert.MajorArcStep25MinorArcBound.kernelCap_nonneg

lemma norm_kernelPolyC_le_kernelCap (x : UC) :
    ‖kernelPolyC x‖ ≤ kernelCap := by
  simpa [kernelCap] using
    (Goldbach.Cert.MajorArcStep25MinorArcBound.norm_kernelPolyC_le_kernelCap (x := x))

/-- The α-integral appearing in the definition of `corr_integral_minor_Q0`. -/
noncomputable def innerMinorQ0 (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ),
    (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α

lemma corr_integral_minor_Q0_eq (X N : ℕ) (Δ : ℝ) :
    corr_integral_minor_Q0 X N Δ
      =
    ∫ β in (0 : ℝ)..(1 : ℝ), kernelPolyC (β : UC) * innerMinorQ0 X N Δ β := by
  rfl

/--
If both shifted exponential sums are uniformly bounded by `M` on the **`Q0`-minor arcs**, then the
corresponding α-integral is bounded by `M^2`.

This is the `majorArcSetQ0` analogue of
`Goldbach.Cert.MajorArcStep25MinorArcBound.norm_innerMinor_le_sq_of_expSum_bound`.
-/
theorem norm_innerMinorQ0_le_sq_of_expSum_bound
    (X N : ℕ) (Δ : ℝ) (M : ℝ) (hM : 0 ≤ M) (β : ℝ)
    (hsub : ∀ {α : ℝ}, α ∈ (majorArcSetQ0 X Δ)ᶜ →
      ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M)
    (hadd : ∀ {α : ℝ}, α ∈ (majorArcSetQ0 X Δ)ᶜ →
      ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M) :
    ‖innerMinorQ0 X N Δ β‖ ≤ M ^ 2 := by
  -- Reuse the Step-25 argument verbatim: it only depends on the set defining the indicator.
  have hconst :
      ∀ α ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖(majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α‖ ≤ M ^ 2 := by
    intro α _hαI
    by_cases hα : α ∈ (majorArcSetQ0 X Δ)ᶜ
    · have hI :
          ‖innerIntegrand X N β α‖ ≤ M ^ 2 := by
        have hfour : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ = 1 := by
          simp [fourier_apply]
        have hmul :
            ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M ^ 2 := by
          have h1 : ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M := hsub (α := α) hα
          have h2 : ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M := hadd (α := α) hα
          have : ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M * M :=
            mul_le_mul h1 h2 (norm_nonneg _) hM
          simpa [pow_two] using this
        calc
          ‖innerIntegrand X N β α‖
              =
            ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                  * expSum X N ((α : UC) - (β : UC))
                  * expSum X N ((α : UC) + (β : UC))‖ := by
                  rfl
          _ =
            ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
              * ‖expSum X N ((α : UC) - (β : UC))‖
              * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                simp [mul_assoc]
          _ = 1 * ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                rw [hfour]
          _ = ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                simp
          _ ≤ M ^ 2 := hmul
      simpa [Set.indicator_of_mem hα] using hI
    · have h0 : (0 : ℝ) ≤ M ^ 2 := by nlinarith [sq_nonneg M]
      have h0' : ‖(0 : ℂ)‖ ≤ M ^ 2 := by simpa using h0
      simpa [Set.indicator_of_notMem hα] using h0'

  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := M ^ 2)
      (f := fun α : ℝ =>
        (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)
      hconst
  simpa [innerMinorQ0] using h

/--
Minor-arc bound reduction for `corr_integral_minor_Q0`:
if the shifted exponential sums are uniformly bounded by `M` on `((majorArcSetQ0 X Δ)ᶜ)`,
then `‖corr_integral_minor_Q0‖ ≤ kernelCap * M^2`.
-/
theorem norm_corr_integral_minor_Q0_le_kernelCap_mul_sq_of_expSum_bound
    (X N : ℕ) (Δ : ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hsub : ∀ {β α : ℝ}, α ∈ (majorArcSetQ0 X Δ)ᶜ →
      ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M)
    (hadd : ∀ {β α : ℝ}, α ∈ (majorArcSetQ0 X Δ)ᶜ →
      ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M) :
    ‖corr_integral_minor_Q0 X N Δ‖ ≤ kernelCap * (M ^ 2) := by
  have houter :
      ∀ β ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖kernelPolyC (β : UC) * innerMinorQ0 X N Δ β‖ ≤ kernelCap * (M ^ 2) := by
    intro β _hβI
    have hK : ‖kernelPolyC (β : UC)‖ ≤ kernelCap :=
      norm_kernelPolyC_le_kernelCap (x := (β : UC))
    have hI : ‖innerMinorQ0 X N Δ β‖ ≤ M ^ 2 :=
      norm_innerMinorQ0_le_sq_of_expSum_bound
        (X := X) (N := N) (Δ := Δ) (M := M) (hM := hM) (β := β)
        (hsub := fun {α} hα => hsub (β := β) (α := α) hα)
        (hadd := fun {α} hα => hadd (β := β) (α := α) hα)
    calc
      ‖kernelPolyC (β : UC) * innerMinorQ0 X N Δ β‖
          = ‖kernelPolyC (β : UC)‖ * ‖innerMinorQ0 X N Δ β‖ := by
              simp
      _ ≤ kernelCap * (M ^ 2) := by
              exact mul_le_mul hK hI (norm_nonneg _) (kernelCap_nonneg)

  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := kernelCap * (M ^ 2))
      (f := fun β : ℝ => kernelPolyC (β : UC) * innerMinorQ0 X N Δ β)
      houter
  simpa [corr_integral_minor_Q0_eq, innerMinorQ0] using h

/-!
## `L²` variant: energy bounds on `expSum`

The sup-norm hypothesis in `norm_corr_integral_minor_Q0_le_kernelCap_mul_sq_of_expSum_bound` is
typically too strong to be provable in the intended analytic pipeline.  The following lemmas
replace it by `L²` energy bounds on `((majorArcSetQ0 X Δ)ᶜ)`, using Cauchy–Schwarz in `α`.
-/

private noncomputable def expSumNormSub (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℝ → ℝ :=
  fun α =>
    (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) - (β : UC))‖) α

private noncomputable def expSumNormAdd (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℝ → ℝ :=
  fun α =>
    (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) + (β : UC))‖) α

private lemma expSumNormSub_nonneg (X N : ℕ) (Δ : ℝ) (β : ℝ) :
    0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] expSumNormSub X N Δ β := by
  refine Filter.Eventually.of_forall ?_
  intro α
  by_cases hα : α ∈ (majorArcSetQ0 X Δ)ᶜ
  · simp [expSumNormSub, Set.indicator_of_mem hα, norm_nonneg]
  · simp [expSumNormSub, Set.indicator_of_notMem hα]

private lemma expSumNormAdd_nonneg (X N : ℕ) (Δ : ℝ) (β : ℝ) :
    0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] expSumNormAdd X N Δ β := by
  refine Filter.Eventually.of_forall ?_
  intro α
  by_cases hα : α ∈ (majorArcSetQ0 X Δ)ᶜ
  · simp [expSumNormAdd, Set.indicator_of_mem hα, norm_nonneg]
  · simp [expSumNormAdd, Set.indicator_of_notMem hα]

private lemma norm_indicator_innerIntegrand_eq_mul_norms (X N : ℕ) (Δ : ℝ) (β : ℝ) (α : ℝ) :
    ‖(majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α‖
      =
    expSumNormSub X N Δ β α * expSumNormAdd X N Δ β α := by
  by_cases hα : α ∈ (majorArcSetQ0 X Δ)ᶜ
  · -- On the set: the indicator is `innerIntegrand`.
    simp [expSumNormSub, expSumNormAdd, Set.indicator_of_mem hα, innerIntegrand, mul_assoc,
      fourier_apply]
  · -- Off the set: both indicators are zero.
    simp [expSumNormSub, expSumNormAdd, Set.indicator_of_notMem hα]

theorem norm_innerMinorQ0_le_of_expSum_l2_bound
    (X N : ℕ) (Δ : ℝ) (M2 : ℝ) (hM2 : 0 ≤ M2) (β : ℝ)
    (hsub : MemLp (expSumNormSub X N Δ β) 2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ))))
    (hadd : MemLp (expSumNormAdd X N Δ β) 2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ))))
    (hsub_sq : ∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSub X N Δ β α) ^ 2 ≤ M2)
    (hadd_sq : ∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAdd X N Δ β α) ^ 2 ≤ M2) :
    ‖innerMinorQ0 X N Δ β‖ ≤ M2 := by
  -- First: `‖∫_{0..1} ...‖ ≤ ∫_{Ι 0 1} ‖...‖`.
  have hnorm :
      ‖innerMinorQ0 X N Δ β‖
        ≤
      ∫ α in Ι (0 : ℝ) (1 : ℝ),
        ‖(majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α‖ := by
    simpa [innerMinorQ0] using
      (intervalIntegral.norm_integral_le_integral_norm_uIoc
        (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun α : ℝ =>
          (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))

  -- Rewrite the norm of the integrand on `((majorArcSetQ0 X Δ)ᶜ)` as a product of norms.
  have hrew :
      (∫ α in Ι (0 : ℝ) (1 : ℝ),
          ‖(majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α‖)
        =
      ∫ α in Ι (0 : ℝ) (1 : ℝ), expSumNormSub X N Δ β α * expSumNormAdd X N Δ β α := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro α
    simpa using norm_indicator_innerIntegrand_eq_mul_norms (X := X) (N := N) (Δ := Δ) (β := β) (α := α)

  -- Cauchy–Schwarz / Hölder on `Ι 0 1` with `p=q=2`.
  have hholder :
      (∫ α in Ι (0 : ℝ) (1 : ℝ), expSumNormSub X N Δ β α * expSumNormAdd X N Δ β α)
        ≤
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSub X N Δ β α) ^ 2)
        *
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAdd X N Δ β α) ^ 2) := by
    -- Apply Hölder with `p=q=2` on the restricted measure.
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      simpa using (Real.HolderConjugate.two_two : (2 : ℝ).HolderConjugate 2)
    have h0sub : 0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] expSumNormSub X N Δ β :=
      expSumNormSub_nonneg (X := X) (N := N) (Δ := Δ) (β := β)
    have h0add : 0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] expSumNormAdd X N Δ β :=
      expSumNormAdd_nonneg (X := X) (N := N) (Δ := Δ) (β := β)
    have hsub' :
        MemLp (expSumNormSub X N Δ β) (ENNReal.ofReal (2 : ℝ))
          (volume.restrict (Ι (0 : ℝ) (1 : ℝ))) := by
      simpa using hsub
    have hadd' :
        MemLp (expSumNormAdd X N Δ β) (ENNReal.ofReal (2 : ℝ))
          (volume.restrict (Ι (0 : ℝ) (1 : ℝ))) := by
      simpa using hadd
    -- Hölder gives an `rpow` statement; rewrite it to `sqrt`.
    have hH :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := volume.restrict (Ι (0 : ℝ) (1 : ℝ))) (p := (2 : ℝ)) (q := (2 : ℝ))
        hpq h0sub h0add (hf := hsub') (hg := hadd')
    -- Simplify the RHS: `x^(1/2) = sqrt x` and `f^2` is nat power.
    simpa [Real.sqrt_eq_rpow, Real.rpow_two, pow_two, mul_assoc] using hH

  -- Combine the three inequalities and use the certified `L²` bounds.
  have hsq_le :
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSub X N Δ β α) ^ 2)
        *
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAdd X N Δ β α) ^ 2)
        ≤
      M2 := by
    have hsub0 :
        0 ≤ ∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSub X N Δ β α) ^ 2 := by
      have : 0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] fun α =>
          (expSumNormSub X N Δ β α) ^ 2 := by
        refine Filter.Eventually.of_forall ?_
        intro α
        exact sq_nonneg _
      simpa using MeasureTheory.integral_nonneg_of_ae this
    have hadd0 :
        0 ≤ ∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAdd X N Δ β α) ^ 2 := by
      have : 0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] fun α =>
          (expSumNormAdd X N Δ β α) ^ 2 := by
        refine Filter.Eventually.of_forall ?_
        intro α
        exact sq_nonneg _
      simpa using MeasureTheory.integral_nonneg_of_ae this
    have hsub_sqrt :
        Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSub X N Δ β α) ^ 2) ≤ Real.sqrt M2 := by
      exact Real.sqrt_le_sqrt hsub_sq
    have hadd_sqrt :
        Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAdd X N Δ β α) ^ 2) ≤ Real.sqrt M2 := by
      exact Real.sqrt_le_sqrt hadd_sq
    have hmul :
        Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSub X N Δ β α) ^ 2)
          *
        Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAdd X N Δ β α) ^ 2)
          ≤
        Real.sqrt M2 * Real.sqrt M2 :=
      mul_le_mul hsub_sqrt hadd_sqrt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have : Real.sqrt M2 * Real.sqrt M2 = M2 := by
      simpa [pow_two] using Real.mul_self_sqrt hM2
    exact le_trans hmul (le_of_eq this)

  calc
    ‖innerMinorQ0 X N Δ β‖
        ≤
      ∫ α in Ι (0 : ℝ) (1 : ℝ),
        ‖(majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α‖ := hnorm
    _ =
      ∫ α in Ι (0 : ℝ) (1 : ℝ), expSumNormSub X N Δ β α * expSumNormAdd X N Δ β α := hrew
    _ ≤
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSub X N Δ β α) ^ 2)
        *
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAdd X N Δ β α) ^ 2) := hholder
    _ ≤ M2 := hsq_le

theorem norm_corr_integral_minor_Q0_le_kernelCap_mul_of_expSum_l2_bound
    (X N : ℕ) (Δ : ℝ) (M2 : ℝ) (hM2 : 0 ≤ M2)
    (hsub :
      ∀ β : ℝ,
        MemLp (expSumNormSub X N Δ β) 2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ)))
          ∧
        (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSub X N Δ β α) ^ 2 ≤ M2))
    (hadd :
      ∀ β : ℝ,
        MemLp (expSumNormAdd X N Δ β) 2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ)))
          ∧
        (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAdd X N Δ β α) ^ 2 ≤ M2)) :
    ‖corr_integral_minor_Q0 X N Δ‖ ≤ kernelCap * M2 := by
  -- Bound the outer integrand pointwise by `kernelCap * M2`.
  have houter :
      ∀ β ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖kernelPolyC (β : UC) * innerMinorQ0 X N Δ β‖ ≤ kernelCap * M2 := by
    intro β _hβI
    have hK : ‖kernelPolyC (β : UC)‖ ≤ kernelCap :=
      norm_kernelPolyC_le_kernelCap (x := (β : UC))
    have hI :
        ‖innerMinorQ0 X N Δ β‖ ≤ M2 := by
      have hsubβ := (hsub β)
      have haddβ := (hadd β)
      exact
        norm_innerMinorQ0_le_of_expSum_l2_bound
          (X := X) (N := N) (Δ := Δ) (M2 := M2) (hM2 := hM2) (β := β)
          (hsub := hsubβ.1) (hadd := haddβ.1) (hsub_sq := hsubβ.2) (hadd_sq := haddβ.2)
    calc
      ‖kernelPolyC (β : UC) * innerMinorQ0 X N Δ β‖
          = ‖kernelPolyC (β : UC)‖ * ‖innerMinorQ0 X N Δ β‖ := by
              simp
      _ ≤ kernelCap * M2 := by
              exact mul_le_mul hK hI (norm_nonneg _) (kernelCap_nonneg)

  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := kernelCap * M2)
      (f := fun β : ℝ => kernelPolyC (β : UC) * innerMinorQ0 X N Δ β)
      houter
  simpa [corr_integral_minor_Q0_eq, innerMinorQ0] using h

end

end Goldbach.Cert.MajorArcModules.MinorQ0Bound
