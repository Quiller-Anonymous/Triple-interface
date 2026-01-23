import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
import Goldbach.Cert.MajorArcModules.BetaInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Deterministic extraction lemma for the ε₂-small (small-β) major-arc term.

This is the small-β analogue of `MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0_eq_sum`:
it rewrites `corr_integral_major_Q0_small` as a **finite** `(q,a)` sum of β-integrals of single-arc
α-integrals.

No analytic number theory is used here; this is measure-theory bookkeeping plus `Set.indicator`
algebra.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallExtraction

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcStep23RamanujanSum

noncomputable section

-- Match the ambient circle type used throughout the major-arc pipeline.
abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
Rewrite the ε₂-small β-integral as a finite `(q,a)` sum.

This is the natural “certificate seam”: once the integrand is reduced to finitely many arcs, one
can bound each arc contribution by explicit inequalities and then sum over `q ≤ Q0`.
-/
theorem corr_integral_major_Q0_small_eq_sum
    (X N : ℕ) (Δ : ℝ) (hsep : SepQ0 X Δ)
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
          volume aβ bβ) :
    corr_integral_major_Q0_small X N Δ
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
      ∫ β in aβ..bβ,
        betaSmallSet.indicator (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β := by
  classical
  -- Expand `innerMajorQ0` as a finite `(q,a)` sum pointwise in β.
  have hRewrite :
      (fun β : ℝ =>
          betaSmallSet.indicator (betaIntegrand X N Δ) β)
        =
      fun β : ℝ =>
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
          betaSmallSet.indicator (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β := by
    funext β
    by_cases hβ : β ∈ betaSmallSet
    · -- On `betaSmallSet`, `indicator` is the identity.
      have hβ' : betaSmallSet.indicator (betaIntegrand X N Δ) β = betaIntegrand X N Δ β := by
        simp [Set.indicator_of_mem hβ]
      -- Use Step 24k extraction for `innerMajorQ0` and distribute multiplication by `kernelPolyC`.
      have hsum :
          innerMajorQ0 X N Δ β
            =
          ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
            ∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α := by
        simpa using
          (innerMajorQ0_eq_sum (X := X) (N := N) (Δ := Δ) (β := β) hsep (hInner β))
      have hprod :
          betaIntegrand X N Δ β
            =
          ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α) := by
        -- Multiply the Step-24k sum identity by the kernel and normalize the finite sums.
        simp [betaIntegrand, hsum, Finset.mul_sum]
      -- Put the indicator back on each term.
      simp [hβ, hprod]
    · -- Off `betaSmallSet`, all indicators vanish.
      have : betaSmallSet.indicator (betaIntegrand X N Δ) β = 0 := by
        simp [Set.indicator_of_notMem hβ]
      -- Every term on the RHS is also zero.
      simp [this, Set.indicator_of_notMem hβ]

  -- Finish by swapping the β-integral with the finite sums.
  unfold corr_integral_major_Q0_small
  -- Use the pointwise rewrite inside the interval integral.
  have hInt :
      (∫ β in aβ..bβ, betaSmallSet.indicator (betaIntegrand X N Δ) β)
        =
      ∫ β in aβ..bβ,
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
          betaSmallSet.indicator (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β) := by
    simp [hRewrite]
  rw [hInt]

  -- Integrability for the `q`-level inner sums (derived from `hOuter`).
  have hq_int :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        IntervalIntegrable
          (fun β : ℝ =>
            ∑ a ∈ Rcop q,
              betaSmallSet.indicator (fun β : ℝ =>
                Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                  (∫ α in (0 : ℝ)..(1 : ℝ),
                    (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
          volume aβ bβ := by
    intro q hq
    have hsum :
        IntervalIntegrable
          (∑ a ∈ Rcop q, fun β : ℝ =>
            betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
          volume aβ bβ := by
      refine
        IntervalIntegrable.sum (μ := volume) (a := aβ) (b := bβ)
          (s := Rcop q)
          (f := fun a β =>
            betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
          ?_
      intro a ha
      exact hOuter q hq a ha
    -- `IntervalIntegrable.sum` returns a function-valued `Finset.sum`; convert to the λ-form.
    have hsum_apply :
        (∑ a ∈ Rcop q, fun β : ℝ =>
            betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
          =
        fun β : ℝ =>
          ∑ a ∈ Rcop q,
            betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β := by
      funext β
      simp
    simpa [hsum_apply] using hsum

  -- Swap β-integral with the finite sums (`q` then `a`).
  calc
    (∫ β in aβ..bβ,
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
          betaSmallSet.indicator (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β))
        =
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∫ β in aβ..bβ,
          (∑ a ∈ Rcop q,
            betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β) := by
        simpa using
          (intervalIntegral.integral_finset_sum
            (a := aβ) (b := bβ) (μ := volume) (s := Finset.Icc (1 : ℕ) Q0)
            (f := fun q β =>
              ∑ a ∈ Rcop q,
                betaSmallSet.indicator (fun β : ℝ =>
                  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                    (∫ α in (0 : ℝ)..(1 : ℝ),
                      (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
            hq_int)
    _ =
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
        ∫ β in aβ..bβ,
          betaSmallSet.indicator (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        have ha_int :
            ∀ a ∈ Rcop q,
              IntervalIntegrable
                (fun β : ℝ =>
                  betaSmallSet.indicator (fun β : ℝ =>
                    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                      (∫ α in (0 : ℝ)..(1 : ℝ),
                        (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
                volume aβ bβ := by
          intro a ha
          exact hOuter q hq a ha
        simpa using
          (intervalIntegral.integral_finset_sum
            (a := aβ) (b := bβ) (μ := volume) (s := Rcop q)
            (f := fun a β =>
              betaSmallSet.indicator (fun β : ℝ =>
                Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                  (∫ α in (0 : ℝ)..(1 : ℝ),
                    (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
            ha_int)

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallExtraction
