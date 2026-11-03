import Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
import Goldbach.Cert.MajorArcStep15Parameters
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Generic major/minor split for a finite-weight circle identity

This module splits the exact finite-weight circle integral over the textbook major arcs and their
complement.  It is pure integration bookkeeping: no estimate and no arithmetic-specific theorem
is assumed.  Both the prime-only and von Mangoldt Route A programs instantiate this same split.
-/

namespace Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit

open scoped Interval

open Complex MeasureTheory AddCircle

open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep15Parameters

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private lemma integral_μ_eq_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : UC → E) :
    (∫ x : UC, f x ∂μ) = ∫ t in (0 : ℝ)..(1 : ℝ), f t := by
  have hhaar : (∫ x : UC, f x ∂μ) = ∫ x : UC, f x := by
    simpa [μ] using (AddCircle.integral_haarAddCircle (T := (1 : ℝ)) (f := f))
  have hvol : (∫ x : UC, f x) = ∫ t in (0 : ℝ)..(1 : ℝ), f t := by
    simpa [zero_add] using
      (AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (t := (0 : ℝ)) (f := f)).symm
  exact hhaar.trans hvol

private lemma integral_μ_eq_intervalIntegral_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UC → E) (t : ℝ) :
    (∫ x : UC, f x ∂μ) = ∫ x in t..(t + 1), f x := by
  have hhaar : (∫ x : UC, f x ∂μ) = ∫ x : UC, f x := by
    simpa [μ] using (AddCircle.integral_haarAddCircle (T := (1 : ℝ)) (f := f))
  have hvol : (∫ x : UC, f x) = ∫ x in t..(t + 1), f x := by
    simpa using
      (AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (t := t) (f := f)).symm
  exact hhaar.trans hvol

private lemma intervalIntegrable_indicator_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E}
    (hf : IntervalIntegrable f volume (0 : ℝ) (1 : ℝ)) :
    IntervalIntegrable (s.indicator f) volume (0 : ℝ) (1 : ℝ) := by
  exact ⟨hf.1.indicator hs, hf.2.indicator hs⟩

private theorem intervalIntegral_eq_major_add_minor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E}
    (hf : IntervalIntegrable f volume (0 : ℝ) (1 : ℝ)) :
    (∫ x in (0 : ℝ)..(1 : ℝ), f x)
      = (∫ x in (0 : ℝ)..(1 : ℝ), s.indicator f x)
        + (∫ x in (0 : ℝ)..(1 : ℝ), sᶜ.indicator f x) := by
  have hMajor : IntervalIntegrable (s.indicator f) volume (0 : ℝ) (1 : ℝ) :=
    intervalIntegrable_indicator_of_intervalIntegrable hs hf
  have hMinor : IntervalIntegrable (sᶜ.indicator f) volume (0 : ℝ) (1 : ℝ) :=
    intervalIntegrable_indicator_of_intervalIntegrable hs.compl hf
  have hsum : s.indicator f + sᶜ.indicator f = f :=
    Set.indicator_self_add_compl s f
  calc
    (∫ x in (0 : ℝ)..(1 : ℝ), f x)
        = ∫ x in (0 : ℝ)..(1 : ℝ), (s.indicator f + sᶜ.indicator f) x := by
          simpa [hsum] using
            (congrArg (fun g : ℝ → E => ∫ x in (0 : ℝ)..(1 : ℝ), g x) hsum.symm)
    _ = (∫ x in (0 : ℝ)..(1 : ℝ), s.indicator f x)
          + (∫ x in (0 : ℝ)..(1 : ℝ), sᶜ.indicator f x) := by
      simpa [Pi.add_apply] using
        (intervalIntegral.integral_add (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
          (f := fun x => s.indicator f x) (g := fun x => sᶜ.indicator f x)
          hMajor hMinor)

private lemma intervalIntegrable_indicator_of_intervalIntegrable_at
    {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E}
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (s.indicator f) volume a b := by
  exact ⟨hf.1.indicator hs, hf.2.indicator hs⟩

private theorem intervalIntegral_eq_set_add_compl_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x)
      = (∫ x in a..b, s.indicator f x)
        + (∫ x in a..b, sᶜ.indicator f x) := by
  have hSet : IntervalIntegrable (s.indicator f) volume a b :=
    intervalIntegrable_indicator_of_intervalIntegrable_at hs hf
  have hCompl : IntervalIntegrable (sᶜ.indicator f) volume a b :=
    intervalIntegrable_indicator_of_intervalIntegrable_at hs.compl hf
  have hsum : s.indicator f + sᶜ.indicator f = f :=
    Set.indicator_self_add_compl s f
  calc
    (∫ x in a..b, f x)
        = ∫ x in a..b, (s.indicator f + sᶜ.indicator f) x := by
          simpa [hsum] using
            (congrArg (fun g : ℝ → E => ∫ x in a..b, g x) hsum.symm)
    _ = (∫ x in a..b, s.indicator f x)
          + (∫ x in a..b, sᶜ.indicator f x) := by
      simpa [Pi.add_apply] using
        (intervalIntegral.integral_add (a := a) (b := b) (μ := volume)
          (f := fun x => s.indicator f x) (g := fun x => sᶜ.indicator f x)
          hSet hCompl)

/-- Real parameterization of the generic finite-weight circle integrand. -/
noncomputable def finiteWeightIntervalIntegrand
    (weight : ℕ → ℝ) (N : ℕ) (alpha : ℝ) : ℂ :=
  finiteWeightCircleIntegrand weight N (alpha : UC)

lemma continuous_finiteWeightIntervalIntegrand
    (weight : ℕ → ℝ) (N : ℕ) :
    Continuous (finiteWeightIntervalIntegrand weight N) := by
  unfold finiteWeightIntervalIntegrand finiteWeightCircleIntegrand
    finiteWeightExponentialSum
  fun_prop

lemma intervalIntegrable_finiteWeightIntervalIntegrand
    (weight : ℕ → ℝ) (N : ℕ) :
    IntervalIntegrable (finiteWeightIntervalIntegrand weight N) volume (0 : ℝ) (1 : ℝ) :=
  (continuous_finiteWeightIntervalIntegrand weight N).intervalIntegrable _ _

/-- The exact finite-weight circle integrand restricted to an arbitrary measurable set. -/
noncomputable def finiteWeightSetIntegral
    (weight : ℕ → ℝ) (N : ℕ) (s : Set ℝ) : ℂ :=
  ∫ alpha in (0 : ℝ)..(1 : ℝ),
    s.indicator (finiteWeightIntervalIntegrand weight N) alpha

/-- The complementary contribution for an arbitrary measurable set. -/
noncomputable def finiteWeightSetComplementIntegral
    (weight : ℕ → ℝ) (N : ℕ) (s : Set ℝ) : ℂ :=
  ∫ alpha in (0 : ℝ)..(1 : ℝ),
    sᶜ.indicator (finiteWeightIntervalIntegrand weight N) alpha

/--
Exact complex split of a finite-weight convolution across any measurable frequency set and its
complement. This is the set-parametric form used by finite `Q0` major arcs.
-/
theorem finiteWeightPairConvolution_cast_eq_set_add_compl
    (weight : ℕ → ℝ) (N : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    (finiteWeightPairConvolution weight N : ℂ)
      = finiteWeightSetIntegral weight N s
        + finiteWeightSetComplementIntegral weight N s := by
  calc
    (finiteWeightPairConvolution weight N : ℂ)
        = finiteWeightCircleIntegral weight N :=
      (finiteWeightCircleIntegral_eq_convolution weight N).symm
    _ = ∫ alpha in (0 : ℝ)..(1 : ℝ), finiteWeightIntervalIntegrand weight N alpha := by
      unfold finiteWeightCircleIntegral finiteWeightIntervalIntegrand
      simpa using
        (integral_μ_eq_intervalIntegral
          (f := fun alpha : UC => finiteWeightCircleIntegrand weight N alpha))
    _ = finiteWeightSetIntegral weight N s
          + finiteWeightSetComplementIntegral weight N s := by
      simpa [finiteWeightSetIntegral, finiteWeightSetComplementIntegral] using
        (intervalIntegral_eq_major_add_minor (s := s) hs
          (intervalIntegrable_finiteWeightIntervalIntegrand weight N))

/-- Real form of the exact split across an arbitrary measurable frequency set. -/
theorem finiteWeightPairConvolution_eq_set_re_add_compl_re
    (weight : ℕ → ℝ) (N : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    finiteWeightPairConvolution weight N
      = (finiteWeightSetIntegral weight N s).re
        + (finiteWeightSetComplementIntegral weight N s).re := by
  have h := congrArg Complex.re
    (finiteWeightPairConvolution_cast_eq_set_add_compl weight N s hs)
  simpa using h

/-- The contribution of a measurable set on the length-one interval beginning at `t`. -/
noncomputable def finiteWeightSetIntegralAt
    (weight : ℕ → ℝ) (N : ℕ) (t : ℝ) (s : Set ℝ) : ℂ :=
  ∫ alpha in t..(t + 1),
    s.indicator (finiteWeightIntervalIntegrand weight N) alpha

/-- The complementary contribution on the length-one interval beginning at `t`. -/
noncomputable def finiteWeightSetComplementIntegralAt
    (weight : ℕ → ℝ) (N : ℕ) (t : ℝ) (s : Set ℝ) : ℂ :=
  ∫ alpha in t..(t + 1),
    sᶜ.indicator (finiteWeightIntervalIntegrand weight N) alpha

/-- Exact set/complement split on any translated fundamental interval of length one. -/
theorem finiteWeightPairConvolution_cast_eq_set_add_compl_at
    (weight : ℕ → ℝ) (N : ℕ) (t : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    (finiteWeightPairConvolution weight N : ℂ)
      = finiteWeightSetIntegralAt weight N t s
        + finiteWeightSetComplementIntegralAt weight N t s := by
  have hInt :
      IntervalIntegrable (finiteWeightIntervalIntegrand weight N) volume t (t + 1) :=
    (continuous_finiteWeightIntervalIntegrand weight N).intervalIntegrable _ _
  calc
    (finiteWeightPairConvolution weight N : ℂ)
        = finiteWeightCircleIntegral weight N :=
      (finiteWeightCircleIntegral_eq_convolution weight N).symm
    _ = ∫ alpha in t..(t + 1), finiteWeightIntervalIntegrand weight N alpha := by
      unfold finiteWeightCircleIntegral finiteWeightIntervalIntegrand
      simpa using
        (integral_μ_eq_intervalIntegral_at
          (f := fun alpha : UC => finiteWeightCircleIntegrand weight N alpha) t)
    _ = finiteWeightSetIntegralAt weight N t s
          + finiteWeightSetComplementIntegralAt weight N t s := by
      simpa [finiteWeightSetIntegralAt, finiteWeightSetComplementIntegralAt] using
        (intervalIntegral_eq_set_add_compl_at (s := s) hs hInt)

/-- Generic major-arc part of the exact circle integral. -/
noncomputable def finiteWeightMajorArcIntegral
    (weight : ℕ → ℝ) (N B : ℕ) (Delta : ℝ) : ℂ :=
  ∫ alpha in (0 : ℝ)..(1 : ℝ),
    (majorArcSetTextbook N B Delta).indicator
      (finiteWeightIntervalIntegrand weight N) alpha

/-- Generic minor-arc part of the exact circle integral. -/
noncomputable def finiteWeightMinorArcIntegral
    (weight : ℕ → ℝ) (N B : ℕ) (Delta : ℝ) : ℂ :=
  ∫ alpha in (0 : ℝ)..(1 : ℝ),
    (majorArcSetTextbook N B Delta)ᶜ.indicator
      (finiteWeightIntervalIntegrand weight N) alpha

/-- Exact complex major/minor split for any finite real weight. -/
theorem finiteWeightPairConvolution_cast_eq_major_add_minor
    (weight : ℕ → ℝ) (N B : ℕ) (Delta : ℝ) :
    (finiteWeightPairConvolution weight N : ℂ)
      = finiteWeightMajorArcIntegral weight N B Delta
        + finiteWeightMinorArcIntegral weight N B Delta := by
  calc
    (finiteWeightPairConvolution weight N : ℂ)
        = finiteWeightCircleIntegral weight N :=
      (finiteWeightCircleIntegral_eq_convolution weight N).symm
    _ = ∫ alpha in (0 : ℝ)..(1 : ℝ), finiteWeightIntervalIntegrand weight N alpha := by
      unfold finiteWeightCircleIntegral finiteWeightIntervalIntegrand
      simpa using
        (integral_μ_eq_intervalIntegral
          (f := fun alpha : UC => finiteWeightCircleIntegrand weight N alpha))
    _ = finiteWeightMajorArcIntegral weight N B Delta
          + finiteWeightMinorArcIntegral weight N B Delta := by
      have hs : MeasurableSet (majorArcSetTextbook N B Delta) :=
        measurableSet_majorArcSetTextbook N B Delta
      simpa [finiteWeightMajorArcIntegral, finiteWeightMinorArcIntegral] using
        (intervalIntegral_eq_major_add_minor (s := majorArcSetTextbook N B Delta) hs
          (intervalIntegrable_finiteWeightIntervalIntegrand weight N))

/-- Real form of the exact generic major/minor split. -/
theorem finiteWeightPairConvolution_eq_major_re_add_minor_re
    (weight : ℕ → ℝ) (N B : ℕ) (Delta : ℝ) :
    finiteWeightPairConvolution weight N
      = (finiteWeightMajorArcIntegral weight N B Delta).re
        + (finiteWeightMinorArcIntegral weight N B Delta).re := by
  have h := congrArg Complex.re
    (finiteWeightPairConvolution_cast_eq_major_add_minor weight N B Delta)
  simpa using h

end

end Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit
