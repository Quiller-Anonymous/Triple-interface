import Goldbach.Cert.MajorArcModules.Q0MajorTailSpec
import Goldbach.Cert.MajorArcModules.BetaInterval
import Mathlib.Analysis.Fourier.AddCircle

/-!
Option 3 preparation: reduce the large-β tail energy bound to a TT*/Parseval statement.

The current `Q0` route records the missing analytic input for the large-β tail as:

`Q0MajorTailSpec.Q0InnerMajorLargeBetaEnergyBound Δ M2`,

which bounds the `L²` mass of `β ↦ innerMajorQ0 X N Δ β` on `betaSmallSetᶜ` inside `[-1/2,1/2]`.

For an engine based on large-sieve/TT* technology, it is more convenient to work with Fourier
coefficients.  Mathlib provides Parseval on an interval `(a,b]` via `fourierCoeffOn`.

This module packages a clean interface:

`Q0InnerMajorLargeBetaTTStarBound Δ M2`,

stating an explicit upper bound on

`∑' k : ℤ, ‖fourierCoeffOn (a<b) (betaSmallSetᶜ.indicator (innerMajorQ0 ...)) k‖^2`.

It then shows that such a TT*/Parseval bound implies the original energy interface
`Q0InnerMajorLargeBetaEnergyBound`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStar

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.Q0MajorTailSpec

noncomputable section

open Goldbach.Cert.MajorArcModules.BetaInterval

private lemma intervalIntegral_eq_setIntegral_Iβ
    {f : ℝ → ℝ} :
    (∫ x in aβ..bβ, f x) = ∫ x in Iβ, f x := by
  -- `aβ ≤ bβ`, so interval integrals agree with set integrals on `Ioc`.
  simpa [Iβ] using (intervalIntegral.integral_of_le (μ := volume) (f := f) hle)

private lemma inv_len_eq_one : (bβ - aβ : ℝ)⁻¹ = 1 :=
  BetaInterval.inv_len_eq_one

/-- The ℂ-valued tail function whose `L²` mass we want to bound. -/
noncomputable def innerMajorTailFn (X N : ℕ) (Δ : ℝ) : ℝ → ℂ :=
  betaSmallSetᶜ.indicator (fun β : ℝ => innerMajorQ0 X N Δ β)

private lemma norm_innerMajorTailFn
    (X N : ℕ) (Δ : ℝ) (β : ℝ) :
    ‖innerMajorTailFn X N Δ β‖ =
      betaSmallSetᶜ.indicator (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖) β := by
  classical
  by_cases hβ : β ∈ betaSmallSetᶜ
  · simp [innerMajorTailFn, hβ]
  · simp [innerMajorTailFn, hβ]

/--
TT*/Parseval interface for the large-β tail: bound the squared ℓ²-norm of the Fourier
coefficients of `innerMajorTailFn` on `Iβ = (-1/2,1/2]`.
-/
structure Q0InnerMajorLargeBetaTTStarBound (Δ M2 : ℝ) : Prop where
  nonneg : 0 ≤ M2
  memLp :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        MemLp (innerMajorTailFn X N Δ) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Iβ)
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        (∑' k : ℤ, ‖fourierCoeffOn hab (innerMajorTailFn X N Δ) k‖ ^ 2) ≤ M2 ^ 2

namespace Q0InnerMajorLargeBetaTTStarBound

private lemma memLp_two_of_memLp_ofReal_two
    {f : ℝ → ℂ} {μ : Measure ℝ}
    (h : MemLp f (ENNReal.ofReal (2 : ℝ)) μ) :
    MemLp f (2 : ENNReal) μ := by
  have hp : (ENNReal.ofReal (2 : ℝ)) = (2 : ENNReal) := by
    norm_num
  simpa [hp] using h

/--
If the squared Fourier-coefficient ℓ²-sum is bounded by `M2^2`, then the tail energy is bounded
by `M2^2` (and hence the `L²` norm is bounded by `M2`).
-/
theorem to_energyBound
    {Δ M2 : ℝ} (h : Q0InnerMajorLargeBetaTTStarBound Δ M2) :
    Q0InnerMajorLargeBetaEnergyBound Δ M2 := by
  classical
  refine ⟨h.nonneg, ?_, ?_⟩
  · -- `MemLp` for the real-valued norm-indicator follows from `MemLp` for the complex function.
    intro X N hX hN
    have hLpC : MemLp (innerMajorTailFn X N Δ) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Iβ) :=
      h.memLp (X := X) (N := N) hX hN
    -- take norms and rewrite `‖innerMajorTailFn‖` as the tail indicator of the norm.
    have hLpR :
        MemLp (fun β : ℝ => ‖innerMajorTailFn X N Δ β‖)
          (ENNReal.ofReal (2 : ℝ)) (volume.restrict Iβ) :=
      hLpC.norm
    -- unfold the definition expected by `Q0MajorTailSpec` (indicator of the norm itself).
    simpa [norm_innerMajorTailFn] using hLpR
  · intro X N hX hN
    -- Apply Parseval on the interval `(aβ,bβ]` and use `bβ-aβ = 1`.
    have hLpC : MemLp (innerMajorTailFn X N Δ) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Iβ) :=
      h.memLp (X := X) (N := N) hX hN
    have hLp2 : MemLp (innerMajorTailFn X N Δ) (2 : ENNReal) (volume.restrict Iβ) :=
      memLp_two_of_memLp_ofReal_two (f := innerMajorTailFn X N Δ) hLpC
    have hParseval :
        (∑' k : ℤ, ‖fourierCoeffOn hab (innerMajorTailFn X N Δ) k‖ ^ 2)
          =
        (bβ - aβ)⁻¹ • ∫ x in aβ..bβ, ‖innerMajorTailFn X N Δ x‖ ^ 2 := by
      simpa [Set.Ioc] using
        (tsum_sq_fourierCoeffOn (a := aβ) (b := bβ) (f := innerMajorTailFn X N Δ) hab hLp2)
    -- Convert the interval integral to a set integral over `Iβ`.
    have hInt :
        (bβ - aβ)⁻¹ • ∫ x in aβ..bβ, ‖innerMajorTailFn X N Δ x‖ ^ 2
          =
        ∫ x in Iβ, ‖innerMajorTailFn X N Δ x‖ ^ 2 := by
      have hlen : (bβ - aβ : ℝ) = 1 := by
        norm_num [aβ, bβ]
      calc
        (bβ - aβ)⁻¹ • ∫ x in aβ..bβ, ‖innerMajorTailFn X N Δ x‖ ^ 2
            =
          (bβ - aβ)⁻¹ * ∫ x in aβ..bβ, ‖innerMajorTailFn X N Δ x‖ ^ 2 := by
              simp [smul_eq_mul]
        _ =
          (1 : ℝ) * ∫ x in aβ..bβ, ‖innerMajorTailFn X N Δ x‖ ^ 2 := by
              simp [hlen]
        _ = ∫ x in aβ..bβ, ‖innerMajorTailFn X N Δ x‖ ^ 2 := by
              simp
        _ = ∫ x in Iβ, ‖innerMajorTailFn X N Δ x‖ ^ 2 := by
              simpa [intervalIntegral_eq_setIntegral_Iβ]
    -- Rewrite `‖innerMajorTailFn‖` as the tail indicator of `‖innerMajorQ0‖`, matching the spec.
    have hnorm :
        (fun β : ℝ => ‖innerMajorTailFn X N Δ β‖ ^ 2)
          =
        (fun β : ℝ =>
          (betaSmallSetᶜ.indicator (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖) β) ^ 2) := by
      funext β
      simp [norm_innerMajorTailFn]
    -- Use the TT* bound to bound the integral.
    have hcoeff : (∑' k : ℤ, ‖fourierCoeffOn hab (innerMajorTailFn X N Δ) k‖ ^ 2) ≤ M2 ^ 2 :=
      h.bound (X := X) (N := N) hX hN
    -- `∑' = integral`, so `integral ≤ M2^2`.
    have hI :
        (∫ x in Iβ,
            (betaSmallSetᶜ.indicator (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖) x) ^ 2)
          ≤ M2 ^ 2 := by
      -- Start from Parseval, then rewrite everything into the desired shape.
      have hEq :
          (∑' k : ℤ, ‖fourierCoeffOn hab (innerMajorTailFn X N Δ) k‖ ^ 2)
            =
          ∫ x in Iβ,
            (betaSmallSetᶜ.indicator (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖) x) ^ 2 := by
        -- `Parseval` + `b-a=1` + `intervalIntegral = setIntegral` + rewrite norms.
        calc
          (∑' k : ℤ, ‖fourierCoeffOn hab (innerMajorTailFn X N Δ) k‖ ^ 2)
              =
            (bβ - aβ)⁻¹ • ∫ x in aβ..bβ, ‖innerMajorTailFn X N Δ x‖ ^ 2 := by
              exact hParseval
          _ = ∫ x in Iβ, ‖innerMajorTailFn X N Δ x‖ ^ 2 := by
              exact hInt
          _ = ∫ x in Iβ, (betaSmallSetᶜ.indicator (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖) x) ^ 2 := by
              simp [hnorm]
      -- conclude by rewriting `hcoeff` along the equality.
      simpa [hEq] using hcoeff
    -- `hI` is exactly the `bound` field expected by `Q0MajorTailSpec`.
    simpa [innerMajorTailFn, norm_innerMajorTailFn] using hI

end Q0InnerMajorLargeBetaTTStarBound

/-!
## A stronger (and easier to target) TT*/Parseval interface

`innerMajorTailFn` is the β-tail indicator of `innerMajorQ0`, so its Fourier coefficients are not
algebraically simple. For certificate/engine work it is often better to bound the **full**
`L²`-mass of `β ↦ innerMajorQ0 X N Δ β` on `Iβ = (-1/2,1/2]` and then use the trivial inequality
`∫_{tail} ≤ ∫_{Iβ}`.

This section packages that stronger interface and shows it implies the tail TT* interface above.
-/

/--
Full-interval TT*/Parseval interface: bound the squared ℓ²-norm of Fourier coefficients of
`β ↦ innerMajorQ0 X N Δ β` on `Iβ = (-1/2,1/2]`.

This is strictly stronger than `Q0InnerMajorLargeBetaTTStarBound`, hence can be used as a drop-in
analytic payload when the tail indicator would otherwise complicate the Fourier side.
-/
structure Q0InnerMajorFullTTStarBound (Δ M2 : ℝ) : Prop where
  nonneg : 0 ≤ M2
  memLp :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        MemLp (fun β : ℝ => innerMajorQ0 X N Δ β) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Iβ)
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        (∑' k : ℤ, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2) ≤ M2 ^ 2

namespace Q0InnerMajorFullTTStarBound

private lemma memLp_two_of_memLp_ofReal_two
    {f : ℝ → ℂ} {μ : Measure ℝ}
    (h : MemLp f (ENNReal.ofReal (2 : ℝ)) μ) :
    MemLp f (2 : ENNReal) μ := by
  have hp : (ENNReal.ofReal (2 : ℝ)) = (2 : ENNReal) := by
    norm_num
  simpa [hp] using h

/--
Full-interval TT* bound ⇒ tail TT* bound (by the trivial domination `‖indicator⋅f‖ ≤ ‖f‖`
and Parseval on `Iβ`).
-/
theorem to_tailTTStarBound
    {Δ M2 : ℝ} (h : Q0InnerMajorFullTTStarBound Δ M2) :
    Q0InnerMajorLargeBetaTTStarBound Δ M2 := by
  classical
  refine ⟨h.nonneg, ?_, ?_⟩
  · intro X N hX hN
    have hLpFull :
        MemLp (fun β : ℝ => innerMajorQ0 X N Δ β) (ENNReal.ofReal (2 : ℝ))
          (volume.restrict Iβ) :=
      h.memLp (X := X) (N := N) hX hN
    have hs : MeasurableSet betaSmallSetᶜ := (measurableSet_betaSmallSet).compl
    -- `innerMajorTailFn` is exactly the tail indicator of `innerMajorQ0`.
    simpa [innerMajorTailFn] using
      (MemLp.indicator (μ := volume.restrict Iβ) (s := betaSmallSetᶜ) (hs := hs) hLpFull)
  · intro X N hX hN
    -- Use Parseval on `Iβ` for the tail function and for the full function.
    have hLpFull :
        MemLp (fun β : ℝ => innerMajorQ0 X N Δ β) (ENNReal.ofReal (2 : ℝ))
          (volume.restrict Iβ) :=
      h.memLp (X := X) (N := N) hX hN
    have hLpTail :
        MemLp (innerMajorTailFn X N Δ) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Iβ) := by
      have hs : MeasurableSet betaSmallSetᶜ := (measurableSet_betaSmallSet).compl
      simpa [innerMajorTailFn] using
        (MemLp.indicator (μ := volume.restrict Iβ) (s := betaSmallSetᶜ) (hs := hs) hLpFull)
    have hLpTail2 : MemLp (innerMajorTailFn X N Δ) (2 : ENNReal) (volume.restrict Iβ) :=
      memLp_two_of_memLp_ofReal_two (f := innerMajorTailFn X N Δ) hLpTail
    have hLpFull2 :
        MemLp (fun β : ℝ => innerMajorQ0 X N Δ β) (2 : ENNReal) (volume.restrict Iβ) :=
      memLp_two_of_memLp_ofReal_two (f := fun β : ℝ => innerMajorQ0 X N Δ β) hLpFull

    have hParseTail :
        (∑' k : ℤ, ‖fourierCoeffOn hab (innerMajorTailFn X N Δ) k‖ ^ 2)
          =
        (bβ - aβ)⁻¹ • ∫ β in aβ..bβ, ‖innerMajorTailFn X N Δ β‖ ^ 2 := by
      simpa [Set.Ioc] using
        (tsum_sq_fourierCoeffOn (a := aβ) (b := bβ) (f := innerMajorTailFn X N Δ) hab hLpTail2)

    have hParseFull :
        (∑' k : ℤ, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
          =
        (bβ - aβ)⁻¹ • ∫ β in aβ..bβ, ‖innerMajorQ0 X N Δ β‖ ^ 2 := by
      simpa [Set.Ioc] using
        (tsum_sq_fourierCoeffOn (a := aβ) (b := bβ) (f := fun β : ℝ => innerMajorQ0 X N Δ β) hab
          hLpFull2)

    -- On `Iβ`, the tail energy is bounded by the full energy.
    have hIntLe :
        (∫ β in aβ..bβ, ‖innerMajorTailFn X N Δ β‖ ^ 2)
          ≤
        (∫ β in aβ..bβ, ‖innerMajorQ0 X N Δ β‖ ^ 2) := by
      -- Work with the restricted measure on `Iβ`.
      let μβ : Measure ℝ := volume.restrict Iβ
      have hIntTail :
          Integrable (fun β : ℝ => ‖innerMajorTailFn X N Δ β‖ ^ (2 : ℕ)) μβ := by
        have hLpNat : MemLp (innerMajorTailFn X N Δ) (2 : ℕ) μβ := by
          -- coercions: `(2 : ℕ)` vs `(2 : ENNReal)`
          simpa [μβ] using hLpTail2
        simpa [pow_two, μβ] using hLpNat.integrable_norm_pow (p := 2) (by decide)
      have hIntFull :
          Integrable (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖ ^ (2 : ℕ)) μβ := by
        have hLpNat : MemLp (fun β : ℝ => innerMajorQ0 X N Δ β) (2 : ℕ) μβ := by
          simpa [μβ] using hLpFull2
        simpa [pow_two, μβ] using hLpNat.integrable_norm_pow (p := 2) (by decide)
      have hmono :
          (fun β : ℝ => ‖innerMajorTailFn X N Δ β‖ ^ (2 : ℕ))
            ≤ᵐ[μβ]
          (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖ ^ (2 : ℕ)) := by
        refine Filter.Eventually.of_forall ?_
        intro β
        by_cases hβ : β ∈ betaSmallSetᶜ
        · simp [innerMajorTailFn, hβ]
        · simp [innerMajorTailFn, hβ]
      -- `∫_{a..b}` agrees with the restricted integral on `Iβ`.
      have hEqTail :
          (∫ β in aβ..bβ, ‖innerMajorTailFn X N Δ β‖ ^ 2)
            =
          ∫ β, ‖innerMajorTailFn X N Δ β‖ ^ (2 : ℕ) ∂μβ := by
        -- interval integral → set integral, then set integral → restricted integral
        simp [intervalIntegral_eq_setIntegral_Iβ, μβ, pow_two]
      have hEqFull :
          (∫ β in aβ..bβ, ‖innerMajorQ0 X N Δ β‖ ^ 2)
            =
          ∫ β, ‖innerMajorQ0 X N Δ β‖ ^ (2 : ℕ) ∂μβ := by
        simp [intervalIntegral_eq_setIntegral_Iβ, μβ, pow_two]
      -- now apply monotonicity on the restricted integral
      have hI :
          (∫ β, ‖innerMajorTailFn X N Δ β‖ ^ (2 : ℕ) ∂μβ)
            ≤
          (∫ β, ‖innerMajorQ0 X N Δ β‖ ^ (2 : ℕ) ∂μβ) := by
        exact MeasureTheory.integral_mono_ae hIntTail hIntFull hmono
      simpa [hEqTail, hEqFull] using hI

    -- Convert the integral inequality into a coefficient-sum inequality using Parseval.
    have hcoef_le :
        (∑' k : ℤ, ‖fourierCoeffOn hab (innerMajorTailFn X N Δ) k‖ ^ 2)
          ≤
        (∑' k : ℤ, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2) := by
      -- `bβ-aβ = 1` so the Parseval prefactor is `1`.
      have hTail' :
          (∑' k : ℤ, ‖fourierCoeffOn hab (innerMajorTailFn X N Δ) k‖ ^ 2)
            =
          ∫ β in aβ..bβ, ‖innerMajorTailFn X N Δ β‖ ^ 2 := by
        calc
          (∑' k : ℤ, ‖fourierCoeffOn hab (innerMajorTailFn X N Δ) k‖ ^ 2)
              =
            (bβ - aβ)⁻¹ • ∫ β in aβ..bβ, ‖innerMajorTailFn X N Δ β‖ ^ 2 := hParseTail
          _ = (1 : ℝ) • ∫ β in aβ..bβ, ‖innerMajorTailFn X N Δ β‖ ^ 2 := by
                have hinv : (bβ - aβ : ℝ)⁻¹ = 1 := inv_len_eq_one
                rw [hinv]
          _ = ∫ β in aβ..bβ, ‖innerMajorTailFn X N Δ β‖ ^ 2 := by
                simp
      have hFull' :
          (∑' k : ℤ, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
            =
          ∫ β in aβ..bβ, ‖innerMajorQ0 X N Δ β‖ ^ 2 := by
        calc
          (∑' k : ℤ, ‖fourierCoeffOn hab (fun β : ℝ => innerMajorQ0 X N Δ β) k‖ ^ 2)
              =
            (bβ - aβ)⁻¹ • ∫ β in aβ..bβ, ‖innerMajorQ0 X N Δ β‖ ^ 2 := hParseFull
          _ = (1 : ℝ) • ∫ β in aβ..bβ, ‖innerMajorQ0 X N Δ β‖ ^ 2 := by
                have hinv : (bβ - aβ : ℝ)⁻¹ = 1 := inv_len_eq_one
                rw [hinv]
          _ = ∫ β in aβ..bβ, ‖innerMajorQ0 X N Δ β‖ ^ 2 := by
                simp
      -- conclude
      -- (rewrite both sides as interval integrals and apply `hIntLe`).
      simpa [hTail', hFull'] using hIntLe

    exact le_trans hcoef_le (h.bound (X := X) (N := N) hX hN)

end Q0InnerMajorFullTTStarBound

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStar
