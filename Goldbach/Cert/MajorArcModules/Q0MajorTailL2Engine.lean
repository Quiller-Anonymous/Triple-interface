import Goldbach.Cert.MajorArcModules.Q0MajorTailSpec
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
`MajorArcModules/Q0MajorTailL2Engine` provides a certificate-friendly interface for the ε₂
large-β “inner major” bound.

Instead of assuming a direct uniform bound on `‖innerMajorQ0 X N Δ β‖` for `β ∈ betaSmallSetᶜ`,
we assume **restricted L² bounds in α** for the shifted exponential sums on `majorArcSetQ0 X Δ`.
One line of Cauchy–Schwarz in `α` then yields the desired uniform bound on `innerMajorQ0`.

This is designed to match the “option (2)” workflow: a generator can target L²-in-α bounds (a
natural large-sieve/TT* output), and Lean turns them into the existing `Q0MajorTailSpec`
interface automatically.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailL2Engine

open scoped Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.Q0MajorTailSpec
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

private noncomputable def expSumNormSubMajor (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℝ → ℝ :=
  fun α =>
    (majorArcSetQ0 X Δ).indicator (fun α => ‖expSum X N ((α : UC) - (β : UC))‖) α

private noncomputable def expSumNormAddMajor (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℝ → ℝ :=
  fun α =>
    (majorArcSetQ0 X Δ).indicator (fun α => ‖expSum X N ((α : UC) + (β : UC))‖) α

private lemma expSumNormSubMajor_nonneg (X N : ℕ) (Δ : ℝ) (β : ℝ) :
    0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] expSumNormSubMajor X N Δ β := by
  refine Filter.Eventually.of_forall ?_
  intro α
  by_cases hα : α ∈ majorArcSetQ0 X Δ
  · simp [expSumNormSubMajor, Set.indicator_of_mem hα, norm_nonneg]
  · simp [expSumNormSubMajor, Set.indicator_of_notMem hα]

private lemma expSumNormAddMajor_nonneg (X N : ℕ) (Δ : ℝ) (β : ℝ) :
    0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] expSumNormAddMajor X N Δ β := by
  refine Filter.Eventually.of_forall ?_
  intro α
  by_cases hα : α ∈ majorArcSetQ0 X Δ
  · simp [expSumNormAddMajor, Set.indicator_of_mem hα, norm_nonneg]
  · simp [expSumNormAddMajor, Set.indicator_of_notMem hα]

private lemma norm_indicator_innerIntegrand_eq_mul_norms (X N : ℕ) (Δ : ℝ) (β : ℝ) (α : ℝ) :
    ‖(majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α‖
      =
    expSumNormSubMajor X N Δ β α * expSumNormAddMajor X N Δ β α := by
  by_cases hα : α ∈ majorArcSetQ0 X Δ
  · -- On the set: the indicator is `innerIntegrand`.
    simp [expSumNormSubMajor, expSumNormAddMajor, Set.indicator_of_mem hα, innerIntegrand,
      mul_assoc, fourier_apply]
  · -- Off the set: both indicators are zero.
    simp [expSumNormSubMajor, expSumNormAddMajor, Set.indicator_of_notMem hα]

theorem norm_innerMajorQ0_le_of_expSum_l2_bound
    (X N : ℕ) (Δ : ℝ) (M2 : ℝ) (hM2 : 0 ≤ M2) (β : ℝ)
    (hsub : MemLp (expSumNormSubMajor X N Δ β) 2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ))))
    (hadd : MemLp (expSumNormAddMajor X N Δ β) 2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ))))
    (hsub_sq : ∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSubMajor X N Δ β α) ^ 2 ≤ M2)
    (hadd_sq : ∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAddMajor X N Δ β α) ^ 2 ≤ M2) :
    ‖innerMajorQ0 X N Δ β‖ ≤ M2 := by
  -- First: `‖∫_{0..1} ...‖ ≤ ∫_{Ι 0 1} ‖...‖`.
  have hnorm :
      ‖innerMajorQ0 X N Δ β‖
        ≤
      ∫ α in Ι (0 : ℝ) (1 : ℝ),
        ‖(majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α‖ := by
    simpa [innerMajorQ0] using
      (intervalIntegral.norm_integral_le_integral_norm_uIoc
        (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun α : ℝ =>
          (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α))

  -- Rewrite the norm of the integrand on `majorArcSetQ0 X Δ` as a product of norms.
  have hrew :
      (∫ α in Ι (0 : ℝ) (1 : ℝ),
          ‖(majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α‖)
        =
      ∫ α in Ι (0 : ℝ) (1 : ℝ), expSumNormSubMajor X N Δ β α * expSumNormAddMajor X N Δ β α := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro α
    simpa using
      norm_indicator_innerIntegrand_eq_mul_norms (X := X) (N := N) (Δ := Δ) (β := β) (α := α)

  -- Cauchy–Schwarz / Hölder on `Ι 0 1` with `p=q=2`.
  have hholder :
      (∫ α in Ι (0 : ℝ) (1 : ℝ), expSumNormSubMajor X N Δ β α * expSumNormAddMajor X N Δ β α)
        ≤
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSubMajor X N Δ β α) ^ 2)
        *
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAddMajor X N Δ β α) ^ 2) := by
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      simpa using (Real.HolderConjugate.two_two : (2 : ℝ).HolderConjugate 2)
    have h0sub :
        0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] expSumNormSubMajor X N Δ β :=
      expSumNormSubMajor_nonneg (X := X) (N := N) (Δ := Δ) (β := β)
    have h0add :
        0 ≤ᵐ[volume.restrict (Ι (0 : ℝ) (1 : ℝ))] expSumNormAddMajor X N Δ β :=
      expSumNormAddMajor_nonneg (X := X) (N := N) (Δ := Δ) (β := β)
    have hsub' :
        MemLp (expSumNormSubMajor X N Δ β) (ENNReal.ofReal (2 : ℝ))
          (volume.restrict (Ι (0 : ℝ) (1 : ℝ))) := by
      simpa using hsub
    have hadd' :
        MemLp (expSumNormAddMajor X N Δ β) (ENNReal.ofReal (2 : ℝ))
          (volume.restrict (Ι (0 : ℝ) (1 : ℝ))) := by
      simpa using hadd
    have hH :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
        (μ := volume.restrict (Ι (0 : ℝ) (1 : ℝ))) (p := (2 : ℝ)) (q := (2 : ℝ))
        hpq h0sub h0add (hf := hsub') (hg := hadd')
    simpa [Real.sqrt_eq_rpow, Real.rpow_two, pow_two, mul_assoc] using hH

  -- Combine Hölder with the assumed squared L² bounds.
  have hsq_le :
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSubMajor X N Δ β α) ^ 2)
        *
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAddMajor X N Δ β α) ^ 2)
        ≤
      M2 := by
    have hsub_sqrt :
        Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSubMajor X N Δ β α) ^ 2) ≤ Real.sqrt M2 := by
      exact Real.sqrt_le_sqrt hsub_sq
    have hadd_sqrt :
        Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAddMajor X N Δ β α) ^ 2) ≤ Real.sqrt M2 := by
      exact Real.sqrt_le_sqrt hadd_sq
    have hmul :
        Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSubMajor X N Δ β α) ^ 2)
          *
        Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAddMajor X N Δ β α) ^ 2)
          ≤
        Real.sqrt M2 * Real.sqrt M2 :=
      mul_le_mul hsub_sqrt hadd_sqrt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have : Real.sqrt M2 * Real.sqrt M2 = M2 := by
      simpa [pow_two] using Real.mul_self_sqrt hM2
    exact le_trans hmul (le_of_eq this)

  calc
    ‖innerMajorQ0 X N Δ β‖
        ≤
      ∫ α in Ι (0 : ℝ) (1 : ℝ),
        ‖(majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α‖ := hnorm
    _ =
      ∫ α in Ι (0 : ℝ) (1 : ℝ), expSumNormSubMajor X N Δ β α * expSumNormAddMajor X N Δ β α := hrew
    _ ≤
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSubMajor X N Δ β α) ^ 2)
        *
      Real.sqrt (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAddMajor X N Δ β α) ^ 2) := hholder
    _ ≤ M2 := hsq_le

/-!
## L² engine interface (large β)

This is the certificate-friendly analytic input: it bounds the restricted L² mass of the shifted
exponential sums on the **Q0 major arcs** for all `β ∈ betaSmallSetᶜ`.
-/

structure Q0InnerMajorLargeBetaL2Bound (Δ M2 : ℝ) : Prop where
  nonneg : 0 ≤ M2
  sub_bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          β ∈ (Ι (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) →
            β ∈ betaSmallSetᶜ →
              MemLp (expSumNormSubMajor X N Δ β) 2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ)))
                ∧
              (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormSubMajor X N Δ β α) ^ 2 ≤ M2)
  add_bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          β ∈ (Ι (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) →
            β ∈ betaSmallSetᶜ →
              MemLp (expSumNormAddMajor X N Δ β) 2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ)))
                ∧
              (∫ α in Ι (0 : ℝ) (1 : ℝ), (expSumNormAddMajor X N Δ β α) ^ 2 ≤ M2)

/--
L²-in-α engine ⇒ the existing ε₂-large interface `Q0InnerMajorLargeBetaBound`.
-/
theorem innerMajorLargeBetaBound_of_L2Bound
    {Δ M2 : ℝ} (h : Q0InnerMajorLargeBetaL2Bound Δ M2) :
    Q0InnerMajorLargeBetaBound Δ M2 := by
  refine ⟨h.nonneg, ?_⟩
  intro X N hX hN β hβI hβLarge
  have hsub := h.sub_bound (X := X) (N := N) hX hN β hβI hβLarge
  have hadd := h.add_bound (X := X) (N := N) hX hN β hβI hβLarge
  exact
    norm_innerMajorQ0_le_of_expSum_l2_bound
      (X := X) (N := N) (Δ := Δ) (M2 := M2) (hM2 := h.nonneg) (β := β)
      (hsub := hsub.1) (hadd := hadd.1) (hsub_sq := hsub.2) (hadd_sq := hadd.2)

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailL2Engine

