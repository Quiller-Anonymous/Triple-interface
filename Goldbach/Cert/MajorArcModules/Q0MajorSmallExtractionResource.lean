import Goldbach.Cert.MajorArcModules.Q0MajorSmallExtraction
import Goldbach.Cert.MajorArcModules.Q0MajorSmallOuterIntegrable

/-!
Resource lemmas for ε₂-small (small-β) extraction.

This file is intentionally **deterministic**: it does not use any analytic number theory.

At the current stage of successive approximation, the ε₂-small assembly is blocked on the
major-arc evaluation step (BMOR Step 20–24 + main-term identification).  To keep progress
incremental and avoid refactors, we package here:

1. a reusable proof that the Step-16 inner integrand `innerIntegrand X N β α` is interval-integrable
   in `α` on `[0,1]` (for each `β`), and
2. a small wrapper around `Q0MajorSmallExtraction.corr_integral_major_Q0_small_eq_sum` that supplies
   the `hInner` hypothesis automatically.

This reduces the remaining ε₂-small work to:
  - providing the per-arc β-integrability hypothesis (`hOuter`), and
  - bounding the resulting finite `(q,a)` sums (certificate generation).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallExtractionResource

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction

open Goldbach.Cert.MajorArcModules.Q0MajorSmallExtraction
open Goldbach.Cert.MajorArcModules.Q0MajorSmallOuterIntegrable
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

private abbrev aβ : ℝ := BetaInterval.aβ
private abbrev bβ : ℝ := BetaInterval.bβ

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_expSum (X N : ℕ) : Continuous (fun γ : UC => expSum X N γ) := by
  classical
  unfold Goldbach.Cert.MajorArcStep12ShiftedExpSums.expSum
  refine continuous_finset_sum (s N) ?_
  intro n _hn
  exact continuous_const.mul ((fourier (T := (1 : ℝ)) (n : ℤ)).continuous)

private lemma continuous_innerIntegrand_alpha (X N : ℕ) (β : ℝ) :
    Continuous (fun α : ℝ => innerIntegrand X N β α) := by
  -- `innerIntegrand` is a product of continuous functions in `α`.
  have hfour : Continuous fun α : ℝ => (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) :=
    ((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous).comp continuous_coe_UC
  have hsub : Continuous fun α : ℝ => expSum X N ((α : UC) - (β : UC)) :=
    (continuous_expSum X N).comp (continuous_coe_UC.sub continuous_const)
  have hadd : Continuous fun α : ℝ => expSum X N ((α : UC) + (β : UC)) :=
    (continuous_expSum X N).comp (continuous_coe_UC.add continuous_const)
  -- rewrite `innerIntegrand` and use continuity of multiplication
  simpa [Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand, mul_assoc] using
    (hfour.mul (hsub.mul hadd))

/-- For each fixed `β`, the Step-16 inner integrand is interval-integrable in `α` on `[0,1]`. -/
theorem innerIntegrand_intervalIntegrable (X N : ℕ) (β : ℝ) :
    IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ) :=
  (continuous_innerIntegrand_alpha (X := X) (N := N) (β := β)).intervalIntegrable _ _

/-- Uniform-in-β version of `innerIntegrand_intervalIntegrable`. -/
theorem innerIntegrand_intervalIntegrable_all (X N : ℕ) :
    ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ) :=
  fun β => innerIntegrand_intervalIntegrable (X := X) (N := N) (β := β)

/--
Convenience wrapper around `corr_integral_major_Q0_small_eq_sum` supplying `hInner`.

The remaining input is the per-arc β-integrability hypothesis `hOuter` needed to swap the β
integral with the finite `(q,a)` sums.
-/
theorem corr_integral_major_Q0_small_eq_sum_of_hOuter
    (X N : ℕ) (Δ : ℝ) (hsep : SepQ0 X Δ)
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
  exact
    Goldbach.Cert.MajorArcModules.Q0MajorSmallExtraction.corr_integral_major_Q0_small_eq_sum
      (X := X) (N := N) (Δ := Δ)
      (hsep := hsep)
      (hInner := innerIntegrand_intervalIntegrable_all (X := X) (N := N))
      (hOuter := hOuter)

 /--
Deterministic `β`-integrability wrapper for `corr_integral_major_Q0_small_eq_sum`.

This supplies both:
- `hInner` via continuity in `α`, and
- `hOuter` via the trivial exponential-sum bound from `ExpSumTrivialBound`.

The only additional assumption is `2 ≤ N`, used to make `log N` well-behaved.
-/
theorem corr_integral_major_Q0_small_eq_sum
    (X N : ℕ) (Δ : ℝ) (hsep : SepQ0 X Δ) (hN2 : 2 ≤ N) :
    corr_integral_major_Q0_small X N Δ
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
      ∫ β in aβ..bβ,
        betaSmallSet.indicator (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β := by
  exact
    corr_integral_major_Q0_small_eq_sum_of_hOuter (X := X) (N := N) (Δ := Δ) (hsep := hsep)
      (hOuter := intervalIntegrable_betaSmall_indicator_singleArc (X := X) (N := N) (Δ := Δ) hN2)

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallExtractionResource
