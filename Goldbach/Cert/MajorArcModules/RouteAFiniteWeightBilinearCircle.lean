import Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit

/-!
# Generic bilinear finite-weight circle identity

The original finite-weight circle API squares one exponential sum.  The fixed-center Vaughan
strategy must instead keep one copy of the balanced von Mangoldt sum intact while pairing it with
one extracted term.  This module provides that bilinear surface for arbitrary finite real weights.

For a measurable frequency set `s`, it proves exactly

`convolution(left, right; N) = integral_s + integral_(s complement)`.

Equivalently, the complementary masked form is the full fixed-center additive convolution minus
the retained-arc integral.  No analytic estimate is used.
-/

namespace Goldbach.Cert.MajorArcModules.RouteAFiniteWeightBilinearCircle

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcStep7FourierOrthogonality

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Additive convolution of two possibly different real weights at the specified center. -/
noncomputable def finiteWeightBilinearConvolution
    (left right : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ primeCandidateSupport N, left n * right (N - n)

@[simp]
theorem finiteWeightBilinearConvolution_self_eq_pairConvolution
    (weight : ℕ → ℝ) (N : ℕ) :
    finiteWeightBilinearConvolution weight weight N
      = finiteWeightPairConvolution weight N :=
  rfl

/-- Circle integrand for the fixed-center bilinear convolution. -/
noncomputable def finiteWeightBilinearCircleIntegrand
    (left right : ℕ → ℝ) (N : ℕ) (alpha : UC) : ℂ :=
  finiteWeightExponentialSum left N alpha
    * finiteWeightExponentialSum right N alpha
    * fourier (T := (1 : ℝ)) (-(N : ℤ)) alpha

/-- Circle integral extracting the bilinear convolution. -/
noncomputable def finiteWeightBilinearCircleIntegral
    (left right : ℕ → ℝ) (N : ℕ) : ℂ :=
  ∫ alpha : UC, finiteWeightBilinearCircleIntegrand left right N alpha ∂μ

private lemma mem_support_sub_of_mem_support
    {N n : ℕ} (hn : n ∈ primeCandidateSupport N) :
    N - n ∈ primeCandidateSupport N := by
  rcases Finset.mem_Icc.mp hn with ⟨hn2, hnN⟩
  have hn_le : n ≤ N := le_trans hnN (Nat.sub_le N 2)
  have h2N : 2 ≤ N := le_trans hn2 hn_le
  have hn_add_two : n + 2 ≤ N := (Nat.le_sub_iff_add_le h2N).mp hnN
  have htwo_add_n : 2 + n ≤ N := by omega
  have hlower : 2 ≤ N - n := (Nat.le_sub_iff_add_le hn_le).mpr htwo_add_n
  have hupper : N - n ≤ N - 2 := Nat.sub_le_sub_left hn2 N
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

private noncomputable def finiteWeightBilinearDoubleSum
    (left right : ℕ → ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
    (left n : ℂ) * (right m : ℂ) * (if n + m = N then 1 else 0)

private lemma finiteWeightBilinearDoubleSum_eq_convolution
    (left right : ℕ → ℝ) (N : ℕ) :
    finiteWeightBilinearDoubleSum left right N
      = (finiteWeightBilinearConvolution left right N : ℂ) := by
  classical
  unfold finiteWeightBilinearDoubleSum finiteWeightBilinearConvolution
  rw [ofReal_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hm : N - n ∈ primeCandidateSupport N := mem_support_sub_of_mem_support hn
  have hn_le : n ≤ N :=
    le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
  have huniq : ∀ {m : ℕ}, n + m = N → m = N - n := by
    intro m hnm
    omega
  have hcollapse :
      (∑ m ∈ primeCandidateSupport N,
          (left n : ℂ) * (right m : ℂ) * (if n + m = N then 1 else 0))
        = (left n : ℂ) * (right (N - n) : ℂ) := by
    have hsum :
        (∑ m ∈ primeCandidateSupport N,
            (left n : ℂ) * (right m : ℂ) * (if n + m = N then 1 else 0))
          = ∑ m ∈ primeCandidateSupport N,
              if n + m = N then (left n : ℂ) * (right m : ℂ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro m hm'
      by_cases hnm : n + m = N <;> simp [hnm]
    rw [hsum, Finset.sum_eq_single (N - n)]
    · rw [if_pos (Nat.add_sub_of_le hn_le)]
    · intro m hm' hne
      by_cases hnm : n + m = N
      · exact (hne (huniq hnm)).elim
      · simp [hnm]
    · intro hnot
      exact (hnot hm).elim
  rw [hcollapse]
  push_cast
  rfl

private lemma delta_eq_integral_fourier {n m N : ℕ} :
    (if n + m = N then (1 : ℂ) else 0)
      = ∫ x : UC,
          (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) x : ℂ) ∂μ := by
  by_cases h : n + m = N
  · have hnm : (n : ℤ) + (m : ℤ) = (N : ℤ) := by
      exact_mod_cast h
    have hidx : (n : ℤ) + (m : ℤ) + (-(N : ℤ)) = 0 := by omega
    rw [Goldbach.Cert.MajorArcStep7FourierOrthogonality.integral_fourier]
    simp [h, hidx]
  · have hidx : (n : ℤ) + (m : ℤ) + (-(N : ℤ)) ≠ 0 := by
      intro hz
      have hnm : (n : ℤ) + (m : ℤ) = (N : ℤ) := by omega
      exact h (by exact_mod_cast hnm)
    rw [Goldbach.Cert.MajorArcStep7FourierOrthogonality.integral_fourier]
    simp [h, hidx]

private lemma finiteWeightBilinearCircleIntegrand_eq_double_sum
    (left right : ℕ → ℝ) (N : ℕ) (alpha : UC) :
    finiteWeightBilinearCircleIntegrand left right N alpha
      = ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
          (left n : ℂ) * (right m : ℂ)
            * fourier (T := (1 : ℝ))
                ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha := by
  classical
  unfold finiteWeightBilinearCircleIntegrand finiteWeightExponentialSum
  calc
    (∑ n ∈ primeCandidateSupport N,
        (left n : ℂ) * fourier (T := (1 : ℝ)) (n : ℤ) alpha)
          * (∑ m ∈ primeCandidateSupport N,
              (right m : ℂ) * fourier (T := (1 : ℝ)) (m : ℤ) alpha)
          * fourier (T := (1 : ℝ)) (-(N : ℤ)) alpha
        = ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
            ((left n : ℂ) * fourier (T := (1 : ℝ)) (n : ℤ) alpha)
              * ((right m : ℂ) * fourier (T := (1 : ℝ)) (m : ℤ) alpha)
              * fourier (T := (1 : ℝ)) (-(N : ℤ)) alpha := by
            rw [Finset.sum_mul_sum]
            simp only [Finset.sum_mul]
    _ = ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
          (left n : ℂ) * (right m : ℂ)
            * fourier (T := (1 : ℝ))
                ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hnm :
          (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ)) alpha : ℂ)
            = fourier (T := (1 : ℝ)) (n : ℤ) alpha
                * fourier (T := (1 : ℝ)) (m : ℤ) alpha := by
        simpa using
          (fourier_add (T := (1 : ℝ)) (m := (n : ℤ)) (n := (m : ℤ)) (x := alpha))
      have hfull :
          (fourier (T := (1 : ℝ))
              ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha : ℂ)
            = fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ)) alpha
                * fourier (T := (1 : ℝ)) (-(N : ℤ)) alpha := by
        simpa [add_assoc] using
          (fourier_add (T := (1 : ℝ))
            (m := (n : ℤ) + (m : ℤ)) (n := (-(N : ℤ))) (x := alpha))
      rw [hfull, hnm]
      ring

private lemma integrable_finiteWeight_bilinear_character
    (left right : ℕ → ℝ) (N n m : ℕ) :
    Integrable
      (fun alpha : UC =>
        (left n : ℂ) * (right m : ℂ)
          * fourier (T := (1 : ℝ))
              ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha)
      μ := by
  have hcont :
      Continuous
        (fun alpha : UC =>
          (left n : ℂ) * (right m : ℂ)
            * fourier (T := (1 : ℝ))
                ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha) := by
    fun_prop
  refine Integrable.of_bound hcont.aestronglyMeasurable
    (‖(left n : ℂ) * (right m : ℂ)‖) ?_
  exact Filter.Eventually.of_forall fun alpha => by
    simp [fourier_apply]

/-- Exact fixed-center circle identity for two finite real weights. -/
theorem finiteWeightBilinearCircleIntegral_eq_convolution
    (left right : ℕ → ℝ) (N : ℕ) :
    finiteWeightBilinearCircleIntegral left right N
      = (finiteWeightBilinearConvolution left right N : ℂ) := by
  classical
  unfold finiteWeightBilinearCircleIntegral
  simp_rw [finiteWeightBilinearCircleIntegrand_eq_double_sum]
  have hinner :
      ∀ n ∈ primeCandidateSupport N,
        Integrable
          (fun alpha : UC =>
            ∑ m ∈ primeCandidateSupport N,
              (left n : ℂ) * (right m : ℂ)
                * fourier (T := (1 : ℝ))
                    ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha)
          μ := by
    intro n hn
    exact integrable_finset_sum (primeCandidateSupport N)
      (fun m _ => integrable_finiteWeight_bilinear_character left right N n m)
  calc
    (∫ alpha : UC,
        ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
          (left n : ℂ) * (right m : ℂ)
            * fourier (T := (1 : ℝ))
                ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha ∂μ)
        = ∑ n ∈ primeCandidateSupport N,
            (∫ alpha : UC,
              ∑ m ∈ primeCandidateSupport N,
                (left n : ℂ) * (right m : ℂ)
                  * fourier (T := (1 : ℝ))
                      ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha ∂μ) := by
          simpa using
            (integral_finset_sum (μ := μ) (s := primeCandidateSupport N)
              (f := fun n (alpha : UC) =>
                ∑ m ∈ primeCandidateSupport N,
                  (left n : ℂ) * (right m : ℂ)
                    * fourier (T := (1 : ℝ))
                        ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha)
              hinner)
    _ = ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
          (∫ alpha : UC,
            (left n : ℂ) * (right m : ℂ)
              * fourier (T := (1 : ℝ))
                  ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha ∂μ) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      simpa using
        (integral_finset_sum (μ := μ) (s := primeCandidateSupport N)
          (f := fun m (alpha : UC) =>
            (left n : ℂ) * (right m : ℂ)
              * fourier (T := (1 : ℝ))
                  ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha)
          (fun m _ => integrable_finiteWeight_bilinear_character left right N n m))
    _ = finiteWeightBilinearDoubleSum left right N := by
      unfold finiteWeightBilinearDoubleSum
      refine Finset.sum_congr rfl ?_
      intro n hn
      refine Finset.sum_congr rfl ?_
      intro m hm
      rw [integral_const_mul]
      rw [← delta_eq_integral_fourier (n := n) (m := m) (N := N)]
    _ = (finiteWeightBilinearConvolution left right N : ℂ) :=
      finiteWeightBilinearDoubleSum_eq_convolution left right N

/-- Real parameterization of the bilinear circle integrand. -/
noncomputable def finiteWeightBilinearIntervalIntegrand
    (left right : ℕ → ℝ) (N : ℕ) (alpha : ℝ) : ℂ :=
  finiteWeightBilinearCircleIntegrand left right N (alpha : UC)

lemma continuous_finiteWeightBilinearIntervalIntegrand
    (left right : ℕ → ℝ) (N : ℕ) :
    Continuous (finiteWeightBilinearIntervalIntegrand left right N) := by
  unfold finiteWeightBilinearIntervalIntegrand finiteWeightBilinearCircleIntegrand
    finiteWeightExponentialSum
  fun_prop

lemma intervalIntegrable_finiteWeightBilinearIntervalIntegrand
    (left right : ℕ → ℝ) (N : ℕ) :
    IntervalIntegrable (finiteWeightBilinearIntervalIntegrand left right N)
      volume (0 : ℝ) (1 : ℝ) :=
  (continuous_finiteWeightBilinearIntervalIntegrand left right N).intervalIntegrable _ _

theorem finiteWeightExponentialSum_add
    (left₁ left₂ : ℕ → ℝ) (N : ℕ) (alpha : UC) :
    finiteWeightExponentialSum (fun n => left₁ n + left₂ n) N alpha
      = finiteWeightExponentialSum left₁ N alpha
        + finiteWeightExponentialSum left₂ N alpha := by
  classical
  unfold finiteWeightExponentialSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro n hn
  push_cast
  ring

theorem finiteWeightBilinearConvolution_add_left
    (left₁ left₂ right : ℕ → ℝ) (N : ℕ) :
    finiteWeightBilinearConvolution (fun n => left₁ n + left₂ n) right N
      = finiteWeightBilinearConvolution left₁ right N
        + finiteWeightBilinearConvolution left₂ right N := by
  classical
  unfold finiteWeightBilinearConvolution
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro n hn
  ring

theorem finiteWeightBilinearIntervalIntegrand_add_left
    (left₁ left₂ right : ℕ → ℝ) (N : ℕ) (alpha : ℝ) :
    finiteWeightBilinearIntervalIntegrand (fun n => left₁ n + left₂ n) right N alpha
      = finiteWeightBilinearIntervalIntegrand left₁ right N alpha
        + finiteWeightBilinearIntervalIntegrand left₂ right N alpha := by
  unfold finiteWeightBilinearIntervalIntegrand finiteWeightBilinearCircleIntegrand
  rw [finiteWeightExponentialSum_add]
  ring

/-- Bilinear contribution from a measurable retained frequency set. -/
noncomputable def finiteWeightBilinearSetIntegral
    (left right : ℕ → ℝ) (N : ℕ) (s : Set ℝ) : ℂ :=
  ∫ alpha in (0 : ℝ)..(1 : ℝ),
    s.indicator (finiteWeightBilinearIntervalIntegrand left right N) alpha

/-- Bilinear contribution from the complement of a measurable retained frequency set. -/
noncomputable def finiteWeightBilinearSetComplementIntegral
    (left right : ℕ → ℝ) (N : ℕ) (s : Set ℝ) : ℂ :=
  ∫ alpha in (0 : ℝ)..(1 : ℝ),
    sᶜ.indicator (finiteWeightBilinearIntervalIntegrand left right N) alpha

theorem finiteWeightBilinearSetComplementIntegral_add_left
    (left₁ left₂ right : ℕ → ℝ) (N : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    finiteWeightBilinearSetComplementIntegral (fun n => left₁ n + left₂ n) right N s
      = finiteWeightBilinearSetComplementIntegral left₁ right N s
        + finiteWeightBilinearSetComplementIntegral left₂ right N s := by
  have h₁ := intervalIntegrable_finiteWeightBilinearIntervalIntegrand left₁ right N
  have h₂ := intervalIntegrable_finiteWeightBilinearIntervalIntegrand left₂ right N
  have h₁Indicator :
      IntervalIntegrable
        (sᶜ.indicator (finiteWeightBilinearIntervalIntegrand left₁ right N))
        volume (0 : ℝ) (1 : ℝ) :=
    ⟨h₁.1.indicator hs.compl, h₁.2.indicator hs.compl⟩
  have h₂Indicator :
      IntervalIntegrable
        (sᶜ.indicator (finiteWeightBilinearIntervalIntegrand left₂ right N))
        volume (0 : ℝ) (1 : ℝ) :=
    ⟨h₂.1.indicator hs.compl, h₂.2.indicator hs.compl⟩
  have hIndicator :
      sᶜ.indicator
          (finiteWeightBilinearIntervalIntegrand (fun n => left₁ n + left₂ n) right N)
        = sᶜ.indicator (finiteWeightBilinearIntervalIntegrand left₁ right N)
          + sᶜ.indicator (finiteWeightBilinearIntervalIntegrand left₂ right N) := by
    funext alpha
    by_cases hα : alpha ∈ sᶜ
    · simp [Set.indicator_of_mem hα,
        finiteWeightBilinearIntervalIntegrand_add_left]
    · simp [Set.indicator_of_notMem hα]
  unfold finiteWeightBilinearSetComplementIntegral
  rw [hIndicator]
  simpa [Pi.add_apply] using
    (intervalIntegral.integral_add (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
      h₁Indicator h₂Indicator)

private lemma circleIntegral_eq_intervalIntegral
    (left right : ℕ → ℝ) (N : ℕ) :
    finiteWeightBilinearCircleIntegral left right N
      = ∫ alpha in (0 : ℝ)..(1 : ℝ),
          finiteWeightBilinearIntervalIntegrand left right N alpha := by
  have hhaar :
      (∫ alpha : UC, finiteWeightBilinearCircleIntegrand left right N alpha ∂μ)
        = ∫ alpha : UC, finiteWeightBilinearCircleIntegrand left right N alpha := by
    simpa [μ] using
      (AddCircle.integral_haarAddCircle (T := (1 : ℝ))
        (f := finiteWeightBilinearCircleIntegrand left right N))
  have hvol :
      (∫ alpha : UC, finiteWeightBilinearCircleIntegrand left right N alpha)
        = ∫ alpha in (0 : ℝ)..(1 : ℝ),
            finiteWeightBilinearCircleIntegrand left right N alpha := by
    simpa [zero_add] using
      (AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (t := (0 : ℝ))
        (f := finiteWeightBilinearCircleIntegrand left right N)).symm
  exact hhaar.trans hvol

/-- Exact split of a fixed-center bilinear convolution across a set and its complement. -/
theorem finiteWeightBilinearConvolution_cast_eq_set_add_compl
    (left right : ℕ → ℝ) (N : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    (finiteWeightBilinearConvolution left right N : ℂ)
      = finiteWeightBilinearSetIntegral left right N s
        + finiteWeightBilinearSetComplementIntegral left right N s := by
  have hf := intervalIntegrable_finiteWeightBilinearIntervalIntegrand left right N
  have hSet :
      IntervalIntegrable
        (s.indicator (finiteWeightBilinearIntervalIntegrand left right N))
        volume (0 : ℝ) (1 : ℝ) :=
    ⟨hf.1.indicator hs, hf.2.indicator hs⟩
  have hCompl :
      IntervalIntegrable
        (sᶜ.indicator (finiteWeightBilinearIntervalIntegrand left right N))
        volume (0 : ℝ) (1 : ℝ) :=
    ⟨hf.1.indicator hs.compl, hf.2.indicator hs.compl⟩
  have hsum :
      s.indicator (finiteWeightBilinearIntervalIntegrand left right N)
        + sᶜ.indicator (finiteWeightBilinearIntervalIntegrand left right N)
      = finiteWeightBilinearIntervalIntegrand left right N :=
    Set.indicator_self_add_compl s _
  calc
    (finiteWeightBilinearConvolution left right N : ℂ)
        = finiteWeightBilinearCircleIntegral left right N :=
          (finiteWeightBilinearCircleIntegral_eq_convolution left right N).symm
    _ = ∫ alpha in (0 : ℝ)..(1 : ℝ),
          finiteWeightBilinearIntervalIntegrand left right N alpha :=
          circleIntegral_eq_intervalIntegral left right N
    _ = ∫ alpha in (0 : ℝ)..(1 : ℝ),
          (s.indicator (finiteWeightBilinearIntervalIntegrand left right N)
            + sᶜ.indicator (finiteWeightBilinearIntervalIntegrand left right N)) alpha := by
          simpa [hsum] using
            (congrArg
              (fun f : ℝ → ℂ => ∫ alpha in (0 : ℝ)..(1 : ℝ), f alpha)
              hsum.symm)
    _ = finiteWeightBilinearSetIntegral left right N s
          + finiteWeightBilinearSetComplementIntegral left right N s := by
      simpa [finiteWeightBilinearSetIntegral, finiteWeightBilinearSetComplementIntegral,
        Pi.add_apply] using
        (intervalIntegral.integral_add (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
          (f := fun alpha =>
            s.indicator (finiteWeightBilinearIntervalIntegrand left right N) alpha)
          (g := fun alpha =>
            sᶜ.indicator (finiteWeightBilinearIntervalIntegrand left right N) alpha)
          hSet hCompl)

/-- Mask-removal form: complementary bilinear mass equals full convolution minus retained arcs. -/
theorem finiteWeightBilinearSetComplementIntegral_eq_convolution_sub_set
    (left right : ℕ → ℝ) (N : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    finiteWeightBilinearSetComplementIntegral left right N s
      = (finiteWeightBilinearConvolution left right N : ℂ)
        - finiteWeightBilinearSetIntegral left right N s := by
  have h := finiteWeightBilinearConvolution_cast_eq_set_add_compl left right N s hs
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm] using h.symm

end

end Goldbach.Cert.MajorArcModules.RouteAFiniteWeightBilinearCircle
