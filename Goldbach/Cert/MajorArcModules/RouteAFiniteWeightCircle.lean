import Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
import Goldbach.Cert.MajorArcStep7FourierOrthogonality

/-!
# Generic finite-weight circle identity

This module isolates the algebraic Fourier identity used by the corrected Route A.  For any real
weight on the complete candidate support `[2, N - 2]`, the additive convolution at `N` is exactly
the `N`th Fourier coefficient of the square of its exponential sum.

The theorem is deliberately independent of prime detection, von Mangoldt estimates, major arcs,
and the obsolete fixed bank.  Prime-only and von Mangoldt circle programs can therefore share the
same checked identity.
-/

namespace Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle

open scoped BigOperators

open Complex MeasureTheory AddCircle

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcStep7FourierOrthogonality

noncomputable section

/-- Additive convolution of a real weight on the complete candidate support. -/
noncomputable def finiteWeightPairConvolution
    (weight : ℕ → ℝ) (N : ℕ) : ℝ :=
  Finset.sum (primeCandidateSupport N) fun n => weight n * weight (N - n)

/-- Finite exponential sum associated with `weight` and target `N`. -/
noncomputable def finiteWeightExponentialSum
    (weight : ℕ → ℝ) (N : ℕ) (alpha : UC) : ℂ :=
  ∑ n ∈ primeCandidateSupport N,
    (weight n : ℂ) * fourier (T := (1 : ℝ)) (n : ℤ) alpha

/-- Integrand extracting the additive convolution at `N`. -/
noncomputable def finiteWeightCircleIntegrand
    (weight : ℕ → ℝ) (N : ℕ) (alpha : UC) : ℂ :=
  finiteWeightExponentialSum weight N alpha ^ 2
    * fourier (T := (1 : ℝ)) (-(N : ℤ)) alpha

/-- Circle integral extracting the additive convolution at `N`. -/
noncomputable def finiteWeightCircleIntegral
    (weight : ℕ → ℝ) (N : ℕ) : ℂ :=
  ∫ alpha : UC, finiteWeightCircleIntegrand weight N alpha ∂μ

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

private noncomputable def finiteWeightPairDoubleSum
    (weight : ℕ → ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
    (weight n : ℂ) * (weight m : ℂ) * (if n + m = N then 1 else 0)

private lemma finiteWeightPairDoubleSum_eq_convolution
    (weight : ℕ → ℝ) (N : ℕ) :
    finiteWeightPairDoubleSum weight N = (finiteWeightPairConvolution weight N : ℂ) := by
  classical
  unfold finiteWeightPairDoubleSum finiteWeightPairConvolution
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
          (weight n : ℂ) * (weight m : ℂ) * (if n + m = N then 1 else 0))
        = (weight n : ℂ) * (weight (N - n) : ℂ) := by
    have hsum :
        (∑ m ∈ primeCandidateSupport N,
            (weight n : ℂ) * (weight m : ℂ) * (if n + m = N then 1 else 0))
          = ∑ m ∈ primeCandidateSupport N,
              if n + m = N then (weight n : ℂ) * (weight m : ℂ) else 0 := by
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

private lemma finiteWeightCircleIntegrand_eq_double_sum
    (weight : ℕ → ℝ) (N : ℕ) (alpha : UC) :
    finiteWeightCircleIntegrand weight N alpha
      = ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
          (weight n : ℂ) * (weight m : ℂ)
            * fourier (T := (1 : ℝ))
                ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha := by
  classical
  unfold finiteWeightCircleIntegrand finiteWeightExponentialSum
  simp only [pow_two]
  calc
    (∑ n ∈ primeCandidateSupport N,
        (weight n : ℂ) * fourier (T := (1 : ℝ)) (n : ℤ) alpha)
          * (∑ m ∈ primeCandidateSupport N,
              (weight m : ℂ) * fourier (T := (1 : ℝ)) (m : ℤ) alpha)
          * fourier (T := (1 : ℝ)) (-(N : ℤ)) alpha
        = ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
            ((weight n : ℂ) * fourier (T := (1 : ℝ)) (n : ℤ) alpha)
              * ((weight m : ℂ) * fourier (T := (1 : ℝ)) (m : ℤ) alpha)
              * fourier (T := (1 : ℝ)) (-(N : ℤ)) alpha := by
            rw [Finset.sum_mul_sum]
            simp only [Finset.sum_mul]
    _ = ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
          (weight n : ℂ) * (weight m : ℂ)
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

private lemma integrable_finiteWeight_pair_character
    (weight : ℕ → ℝ) (N n m : ℕ) :
    Integrable
      (fun alpha : UC =>
        (weight n : ℂ) * (weight m : ℂ)
          * fourier (T := (1 : ℝ))
              ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha)
      μ := by
  have hcont :
      Continuous
        (fun alpha : UC =>
          (weight n : ℂ) * (weight m : ℂ)
            * fourier (T := (1 : ℝ))
                ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha) := by
    fun_prop
  refine Integrable.of_bound hcont.aestronglyMeasurable
    (‖(weight n : ℂ) * (weight m : ℂ)‖) ?_
  exact Filter.Eventually.of_forall fun alpha => by
    simp [norm_mul, fourier_apply]

/-- Generic exact circle identity for a finite real weight. -/
theorem finiteWeightCircleIntegral_eq_convolution
    (weight : ℕ → ℝ) (N : ℕ) :
    finiteWeightCircleIntegral weight N = (finiteWeightPairConvolution weight N : ℂ) := by
  classical
  unfold finiteWeightCircleIntegral
  simp_rw [finiteWeightCircleIntegrand_eq_double_sum]
  have hinner :
      ∀ n ∈ primeCandidateSupport N,
        Integrable
          (fun alpha : UC =>
            ∑ m ∈ primeCandidateSupport N,
              (weight n : ℂ) * (weight m : ℂ)
                * fourier (T := (1 : ℝ))
                    ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha)
          μ := by
    intro n hn
    exact integrable_finset_sum (primeCandidateSupport N)
      (fun m _ => integrable_finiteWeight_pair_character weight N n m)
  calc
    (∫ alpha : UC,
        ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
          (weight n : ℂ) * (weight m : ℂ)
            * fourier (T := (1 : ℝ))
                ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha ∂μ)
        = ∑ n ∈ primeCandidateSupport N,
            (∫ alpha : UC,
              ∑ m ∈ primeCandidateSupport N,
                (weight n : ℂ) * (weight m : ℂ)
                  * fourier (T := (1 : ℝ))
                      ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha ∂μ) := by
          simpa using
            (integral_finset_sum (μ := μ) (s := primeCandidateSupport N)
              (f := fun n (alpha : UC) =>
                ∑ m ∈ primeCandidateSupport N,
                  (weight n : ℂ) * (weight m : ℂ)
                    * fourier (T := (1 : ℝ))
                        ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha)
              hinner)
    _ = ∑ n ∈ primeCandidateSupport N, ∑ m ∈ primeCandidateSupport N,
          (∫ alpha : UC,
            (weight n : ℂ) * (weight m : ℂ)
              * fourier (T := (1 : ℝ))
                  ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha ∂μ) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      simpa using
        (integral_finset_sum (μ := μ) (s := primeCandidateSupport N)
          (f := fun m (alpha : UC) =>
            (weight n : ℂ) * (weight m : ℂ)
              * fourier (T := (1 : ℝ))
                  ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) alpha)
          (fun m _ => integrable_finiteWeight_pair_character weight N n m))
    _ = finiteWeightPairDoubleSum weight N := by
      unfold finiteWeightPairDoubleSum
      refine Finset.sum_congr rfl ?_
      intro n hn
      refine Finset.sum_congr rfl ?_
      intro m hm
      rw [integral_const_mul]
      rw [← delta_eq_integral_fourier (n := n) (m := m) (N := N)]
    _ = (finiteWeightPairConvolution weight N : ℂ) :=
      finiteWeightPairDoubleSum_eq_convolution weight N

end

end Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
