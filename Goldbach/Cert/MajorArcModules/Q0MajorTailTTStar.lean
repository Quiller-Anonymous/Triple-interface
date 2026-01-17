import Goldbach.Cert.MajorArcModules.Q0MajorTailSpec
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

private abbrev aβ : ℝ := (-( (2 : ℝ)⁻¹) : ℝ)
private abbrev bβ : ℝ := ((2 : ℝ)⁻¹ : ℝ)
private abbrev Iβ : Set ℝ := Set.Ioc aβ bβ

private lemma hab : aβ < bβ := by
  norm_num [aβ, bβ]

private lemma hle : aβ ≤ bβ := le_of_lt hab

private lemma Iβ_eq : Iβ = Set.Ioc aβ bβ := rfl

private lemma measurableSet_Iβ : MeasurableSet Iβ := by
  simp [Iβ]

private lemma intervalIntegral_eq_setIntegral_Iβ
    {f : ℝ → ℝ} :
    (∫ x in aβ..bβ, f x) = ∫ x in Iβ, f x := by
  -- `aβ ≤ bβ`, so interval integrals agree with set integrals on `Ioc`.
  simpa [Iβ_eq] using (intervalIntegral.integral_of_le (μ := volume) (f := f) hle)

private lemma inv_len_eq_one : (bβ - aβ : ℝ)⁻¹ = 1 := by
  norm_num [aβ, bβ]

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

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStar
