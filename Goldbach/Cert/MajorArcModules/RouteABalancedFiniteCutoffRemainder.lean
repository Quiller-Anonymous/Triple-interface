import Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffCircle

/-!
# Concrete finite-cutoff remainder

The finite-cutoff circle module defines its remainder algebraically. This module identifies that
remainder with an explicit interval integral: the exact balanced circle integrand minus the sum of
its low-denominator rational-arc restrictions. The finite sum is a mask rather than an unproved
set union, so the identity does not depend on arc-disjointness.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffRemainder

open scoped BigOperators

open Complex MeasureTheory

open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedQ0SeamSafeSplit
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffCircle

noncomputable section

/-- Sum of the low-denominator arc-restricted integrands at one circle frequency. -/
noncomputable def balancedFiniteCutoffMajorMaskIntegrand
    (L N Q : ℕ) (Delta : ℝ) (alpha : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ a ∈ Rcop q,
    (arcSetTextbook N q a Delta).indicator
      (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha

/-- Explicit oscillatory remainder after subtracting the finite low-arc mask pointwise. -/
noncomputable def balancedFiniteCutoffRemainderIntegral
    (L N Q : ℕ) (Delta : ℝ) : ℂ :=
  ∫ alpha in balancedQ0FundamentalStart N Delta..
      (balancedQ0FundamentalStart N Delta + 1),
    (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N alpha
      - balancedFiniteCutoffMajorMaskIntegrand L N Q Delta alpha)

private lemma intervalIntegrable_arcIndicator_at
    (L N q a : ℕ) (Delta u v : ℝ) :
    IntervalIntegrable
      ((arcSetTextbook N q a Delta).indicator
        (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N))
      volume u v := by
  have hf :
      IntervalIntegrable
        (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N)
        volume u v :=
    (continuous_finiteWeightIntervalIntegrand
      (balancedVonMangoldtWeight L N) N).intervalIntegrable _ _
  exact ⟨hf.1.indicator (measurableSet_arcSetTextbook N q a Delta),
    hf.2.indicator (measurableSet_arcSetTextbook N q a Delta)⟩

private lemma intervalIntegrable_balancedFiniteCutoffMajorMaskIntegrand
    (L N Q : ℕ) (Delta u v : ℝ) :
    IntervalIntegrable
      (balancedFiniteCutoffMajorMaskIntegrand L N Q Delta) volume u v := by
  have hqInt :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q,
        IntervalIntegrable
          (fun alpha : ℝ => ∑ a ∈ Rcop q,
            (arcSetTextbook N q a Delta).indicator
              (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha)
          volume u v := by
    intro q hq
    have hsum := IntervalIntegrable.sum (μ := volume) (a := u) (b := v)
      (s := Rcop q)
      (f := fun a alpha =>
        (arcSetTextbook N q a Delta).indicator
          (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha)
      (fun a ha => intervalIntegrable_arcIndicator_at L N q a Delta u v)
    have hsumFun :
        (∑ a ∈ Rcop q, fun alpha : ℝ =>
          (arcSetTextbook N q a Delta).indicator
            (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha)
          = fun alpha : ℝ => ∑ a ∈ Rcop q,
              (arcSetTextbook N q a Delta).indicator
                (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha := by
      funext alpha
      simp
    rw [hsumFun] at hsum
    exact hsum
  have hsum := IntervalIntegrable.sum (μ := volume) (a := u) (b := v)
    (s := Finset.Icc (1 : ℕ) Q)
    (f := fun q alpha => ∑ a ∈ Rcop q,
      (arcSetTextbook N q a Delta).indicator
        (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha)
    hqInt
  have hsumFun :
      (∑ q ∈ Finset.Icc (1 : ℕ) Q, fun alpha : ℝ => ∑ a ∈ Rcop q,
        (arcSetTextbook N q a Delta).indicator
          (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha)
        = balancedFiniteCutoffMajorMaskIntegrand L N Q Delta := by
    funext alpha
    simp [balancedFiniteCutoffMajorMaskIntegrand]
  rw [hsumFun] at hsum
  exact hsum

/-- The finite low-arc sum is exactly the integral of the finite low-arc mask. -/
theorem balancedVonMangoldtMajorArcUpToIntegral_eq_maskIntegral
    (L N Q : ℕ) (Delta : ℝ) :
    balancedVonMangoldtMajorArcUpToIntegral L N Q Delta
      = ∫ alpha in balancedQ0FundamentalStart N Delta..
          (balancedQ0FundamentalStart N Delta + 1),
        balancedFiniteCutoffMajorMaskIntegrand L N Q Delta alpha := by
  classical
  let u : ℝ := balancedQ0FundamentalStart N Delta
  let v : ℝ := balancedQ0FundamentalStart N Delta + 1
  have hqInt :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q,
        IntervalIntegrable
          (fun alpha : ℝ => ∑ a ∈ Rcop q,
            (arcSetTextbook N q a Delta).indicator
              (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha)
          volume u v := by
    intro q hq
    have haInt :
        ∀ a ∈ Rcop q,
          IntervalIntegrable
            ((arcSetTextbook N q a Delta).indicator
              (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N))
            volume u v := by
      intro a ha
      exact intervalIntegrable_arcIndicator_at L N q a Delta u v
    have hsum := IntervalIntegrable.sum (μ := volume) (a := u) (b := v)
      (s := Rcop q)
      (f := fun a alpha =>
        (arcSetTextbook N q a Delta).indicator
          (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha)
      haInt
    have hsumFun :
        (∑ a ∈ Rcop q, fun alpha : ℝ =>
          (arcSetTextbook N q a Delta).indicator
            (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha)
          = fun alpha : ℝ => ∑ a ∈ Rcop q,
              (arcSetTextbook N q a Delta).indicator
                (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha := by
      funext alpha
      simp
    rw [hsumFun] at hsum
    exact hsum
  symm
  calc
    (∫ alpha in u..v, balancedFiniteCutoffMajorMaskIntegrand L N Q Delta alpha)
        = ∑ q ∈ Finset.Icc (1 : ℕ) Q,
            ∫ alpha in u..v, ∑ a ∈ Rcop q,
              (arcSetTextbook N q a Delta).indicator
                (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha := by
              simpa [balancedFiniteCutoffMajorMaskIntegrand] using
                (intervalIntegral.integral_finset_sum
                  (a := u) (b := v) (μ := volume)
                  (s := Finset.Icc (1 : ℕ) Q)
                  (f := fun q alpha => ∑ a ∈ Rcop q,
                    (arcSetTextbook N q a Delta).indicator
                      (finiteWeightIntervalIntegrand
                        (balancedVonMangoldtWeight L N) N) alpha) hqInt)
    _ = ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ a ∈ Rcop q,
          ∫ alpha in u..v,
            (arcSetTextbook N q a Delta).indicator
              (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            have haInt :
                ∀ a ∈ Rcop q,
                  IntervalIntegrable
                    ((arcSetTextbook N q a Delta).indicator
                      (finiteWeightIntervalIntegrand
                        (balancedVonMangoldtWeight L N) N))
                    volume u v := by
              intro a ha
              exact intervalIntegrable_arcIndicator_at L N q a Delta u v
            simpa using
              (intervalIntegral.integral_finset_sum
                (a := u) (b := v) (μ := volume) (s := Rcop q)
                (f := fun a alpha =>
                  (arcSetTextbook N q a Delta).indicator
                    (finiteWeightIntervalIntegrand
                      (balancedVonMangoldtWeight L N) N) alpha) haInt)
    _ = balancedVonMangoldtMajorArcUpToIntegral L N Q Delta := by
          rfl

private theorem balancedVonMangoldtPairConvolution_cast_eq_shiftedIntegral
    (L N : ℕ) (Delta : ℝ) :
    (balancedVonMangoldtPairConvolution L N : ℂ)
      = ∫ alpha in balancedQ0FundamentalStart N Delta..
          (balancedQ0FundamentalStart N Delta + 1),
        finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N alpha := by
  have h := finiteWeightPairConvolution_cast_eq_set_add_compl_at
    (balancedVonMangoldtWeight L N) N
    (balancedQ0FundamentalStart N Delta) (∅ : Set ℝ) MeasurableSet.empty
  simpa [balancedVonMangoldtPairConvolution, finiteWeightSetIntegralAt,
    finiteWeightSetComplementIntegralAt] using h

/-- The algebraic finite-cutoff remainder is the explicit oscillatory remainder integral. -/
theorem balancedVonMangoldtAfterMajorUpToRemainder_eq_integral
    (L N Q : ℕ) (Delta : ℝ) :
    balancedVonMangoldtAfterMajorUpToRemainder L N Q Delta
      = balancedFiniteCutoffRemainderIntegral L N Q Delta := by
  let u : ℝ := balancedQ0FundamentalStart N Delta
  let v : ℝ := balancedQ0FundamentalStart N Delta + 1
  let f : ℝ → ℂ :=
    finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N
  let m : ℝ → ℂ := balancedFiniteCutoffMajorMaskIntegrand L N Q Delta
  have hf : IntervalIntegrable f volume u v := by
    simpa [f] using
      (continuous_finiteWeightIntervalIntegrand
        (balancedVonMangoldtWeight L N) N).intervalIntegrable u v
  have hm : IntervalIntegrable m volume u v := by
    simpa [m] using
      intervalIntegrable_balancedFiniteCutoffMajorMaskIntegrand L N Q Delta u v
  rw [balancedVonMangoldtAfterMajorUpToRemainder]
  rw [balancedVonMangoldtPairConvolution_cast_eq_shiftedIntegral L N Delta]
  rw [balancedVonMangoldtMajorArcUpToIntegral_eq_maskIntegral L N Q Delta]
  rw [show balancedFiniteCutoffRemainderIntegral L N Q Delta
      = ∫ alpha in u..v, (f - m) alpha by rfl]
  simpa [Pi.sub_apply] using (intervalIntegral.integral_sub hf hm).symm

end

end Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffRemainder
