import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Cert.MajorArcModules.ArcSetBounds
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStar
import Goldbach.Cert.MajorArcStep16CircleToInterval
import Goldbach.Cert.MajorArcStep7FourierOrthogonality
import Goldbach.Cert.MajorArcStep12ShiftedExpSums
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Mean-zero (alias-suppression) bookkeeping for the option-3 ε₂-large tail plan.

This module packages the deterministic decomposition suggested in the notes:

* `W(α)` is the (hard) `Q0` major-arc indicator weight in `α`,
* `c = ∫_0^1 W(α)dα` is its constant Fourier mode,
* `W∘(α) = W(α) - c` is mean-zero,
* `innerMajorQ0 = innerMajorQ0∘ + c * innerFull`, where `innerFull` is the full α-integral with no
  major-arc restriction.

The point is to isolate the `h=0` mode as a separate remainder term when using hybrid/large-sieve
technology for the mean-zero part.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.ArcSetBounds
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep12ShiftedExpSums

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-!
## The α-weight and its constant mode
-/

noncomputable def majorArcWeight (X : ℕ) (Δ : ℝ) : ℝ → ℝ :=
  (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator (fun _ => (1 : ℝ))

noncomputable def majorArcConstMode (X : ℕ) (Δ : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α

noncomputable def majorArcWeightBalanced (X : ℕ) (Δ : ℝ) : ℝ → ℝ :=
  fun α => majorArcWeight X Δ α - majorArcConstMode X Δ

-- TODO(option-3): add a deterministic bound `majorArcConstMode X Δ ≤ (2*Δ*Q0)/X`.

lemma majorArcWeightBalanced_mean_zero (X : ℕ) (Δ : ℝ) :
    (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeightBalanced X Δ α) = 0 := by
  unfold majorArcWeightBalanced majorArcConstMode
  -- `∫ (W - ∫ W) = (∫ W) - (∫ W)`.
  have hW :
      IntervalIntegrable (fun α : ℝ => majorArcWeight X Δ α) volume (0 : ℝ) (1 : ℝ) := by
    -- bounded measurable function on a compact interval
    have hs : MeasurableSet (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ) :=
      Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0_measurableSet (X := X) (Δ := Δ)
    -- indicator of a constant is interval-integrable
    have : IntervalIntegrable ((Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
        (fun _α : ℝ => (1 : ℝ))) volume (0 : ℝ) (1 : ℝ) := by
      refine Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
        (s := Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ) hs ?_
      simpa using (intervalIntegrable_const : IntervalIntegrable (fun _α : ℝ => (1 : ℝ)) volume (0 : ℝ) (1 : ℝ))
    simpa [majorArcWeight] using this
  have hconst :
      IntervalIntegrable (fun _α : ℝ => (∫ (α : ℝ) in 0..1, majorArcWeight X Δ α)) volume (0 : ℝ) (1 : ℝ) := by
    simpa using (intervalIntegrable_const : IntervalIntegrable (fun _α : ℝ => (∫ (α : ℝ) in 0..1, majorArcWeight X Δ α)) volume (0 : ℝ) (1 : ℝ))
  have hsub :
      (∫ α in (0 : ℝ)..(1 : ℝ),
          majorArcWeight X Δ α - (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α))
        =
      (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α)
        -
      (∫ α in (0 : ℝ)..(1 : ℝ), (fun _ : ℝ => (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α)) α) := by
    simpa [Pi.sub_apply] using
      (intervalIntegral.integral_sub (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
        (f := fun α : ℝ => majorArcWeight X Δ α)
        (g := fun _α : ℝ => (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α))
        hW hconst)
  -- compute the constant integral and finish
  have hconstInt :
      (∫ α in (0 : ℝ)..(1 : ℝ), (fun _ : ℝ => (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α)) α)
        =
      ∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α := by
    simpa using (intervalIntegral.integral_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (c := (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α)))
  calc
    (∫ α in (0 : ℝ)..(1 : ℝ),
        majorArcWeight X Δ α - (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α))
        =
      (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α)
        -
      (∫ α in (0 : ℝ)..(1 : ℝ), (fun _ : ℝ => (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α)) α) := hsub
    _ =
      (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α)
        -
      (∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeight X Δ α) := by simpa [hconstInt]
    _ = 0 := by ring

/-!
## Decomposing `innerMajorQ0` into mean-zero + remainder
-/

noncomputable def innerFull (X N : ℕ) (β : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ), Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α

noncomputable def innerMajorQ0Balanced (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ),
    ((majorArcWeightBalanced X Δ α : ℝ) : ℂ)
      * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α

noncomputable def innerMajorQ0Remainder (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  ((majorArcConstMode X Δ : ℝ) : ℂ) * innerFull X N β

lemma innerMajorQ0_eq_balanced_add_remainder
    (X N : ℕ) (Δ : ℝ) (β : ℝ)
    (hInt : IntervalIntegrable (fun α : ℝ =>
      Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ)) :
    innerMajorQ0 X N Δ β = innerMajorQ0Balanced X N Δ β + innerMajorQ0Remainder X N Δ β := by
  classical
  -- Expand the indicator, then use `W = (W - c) + c` and linearity of the interval integral.
  set W : ℝ → ℝ := majorArcWeight X Δ
  set c : ℝ := majorArcConstMode X Δ
  have hs : MeasurableSet (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ) :=
    Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0_measurableSet (X := X) (Δ := Δ)
  have hWInt :
      IntervalIntegrable
        ((Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
          (fun α : ℝ =>
            Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α))
        volume (0 : ℝ) (1 : ℝ) :=
    Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
      (s := Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ) hs hInt

  have hWmul :
      (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
          (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
        =
      fun α : ℝ => ((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α := by
    funext α
    by_cases hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ
    · simp [W, majorArcWeight, hα]
    · simp [W, majorArcWeight, hα]

  -- Now expand `W = (W - c) + c` pointwise.
  have hsplit :
      (fun α : ℝ => ((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
        =
      (fun α : ℝ =>
          (((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
            -
          (((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α))
        +
      (fun α : ℝ => ((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) := by
    funext α
    -- `(A - B) + B = A`
    simpa [Pi.add_apply] using
      (sub_add_cancel
        (((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
        (((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)).symm

  -- Rewrite `innerMajorQ0` and split the interval integral.
  unfold innerMajorQ0Balanced innerMajorQ0Remainder innerFull majorArcWeightBalanced majorArcConstMode
  have hInt1 :
      IntervalIntegrable
        (fun α : ℝ =>
          (((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
            -
          (((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α))
        volume (0 : ℝ) (1 : ℝ) := by
    -- bounded multiplier `(W-c)` times an interval-integrable function
    -- (use `IntervalIntegrable.mul_continuousOn`-style lemma via `IntegrableOn` fallback).
    -- We keep it simple by using `hInt.indicator` twice: `W` is an indicator and `c` is constant.
    -- A conservative way: each of `W*f` and `c*f` is interval-integrable, hence so is the difference.
    have hWf :
        IntervalIntegrable
          (fun α : ℝ => ((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ) := by
      -- this is the same as the indicator integrable function we started from
      simpa [hWmul] using hWInt
    have hcf :
        IntervalIntegrable
          (fun α : ℝ => ((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ) := by
      simpa [mul_assoc] using hInt.const_mul ((c : ℂ))
    exact hWf.sub hcf
  have hInt2 :
      IntervalIntegrable
        (fun α : ℝ => ((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
        volume (0 : ℝ) (1 : ℝ) := by
    simpa [mul_assoc] using hInt.const_mul ((c : ℂ))

  -- Finally, split the integral.
  calc
    Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.innerMajorQ0 X N Δ β
        =
      ∫ α in (0 : ℝ)..(1 : ℝ),
        ((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α := by
          simp [Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.innerMajorQ0, hWmul]
    _ =
      (∫ α in (0 : ℝ)..(1 : ℝ),
          (((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
            -
          (((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α))
        +
      (∫ α in (0 : ℝ)..(1 : ℝ),
          ((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) := by
          -- use `hsplit` and linearity
          have hadd :=
            intervalIntegral.integral_add (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
              (f := fun α : ℝ =>
                (((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
                  -
                (((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α))
              (g := fun α : ℝ => ((c : ℝ) : ℂ) *
                Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
              hInt1 hInt2
          simpa [hsplit, Pi.add_apply] using hadd
    _ =
      innerMajorQ0Balanced X N Δ β + ((c : ℝ) : ℂ) * innerFull X N β := by
          -- rewrite the first integral as the balanced one, and pull out `c` from the second.
          have hbal :
              (∫ α in (0 : ℝ)..(1 : ℝ),
                  (((W α : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
                    -
                  (((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α))
                =
              innerMajorQ0Balanced X N Δ β := by
                -- `((W-c):ℂ) * f = (W:ℂ)*f - (c:ℂ)*f`
                unfold innerMajorQ0Balanced majorArcWeightBalanced majorArcConstMode
                simp [W, c, majorArcConstMode, majorArcWeight, sub_mul]
          -- second integral: constant multiplier
          have hconst :
              (∫ α in (0 : ℝ)..(1 : ℝ),
                  ((c : ℝ) : ℂ) * Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
                =
              ((c : ℝ) : ℂ) * innerFull X N β := by
            simp [innerFull, intervalIntegral.integral_const_mul, mul_assoc]
          simpa [hbal, hconst, add_assoc]

/-!
## Full α-integral (orthogonality) and a safe deterministic bound
-/

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
