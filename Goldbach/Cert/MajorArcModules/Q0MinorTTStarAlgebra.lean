import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
import Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource
import Goldbach.Cert.MajorArcStep16CircleToInterval
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Analysis.Fourier.AddCircle

/-!
TT*/Parseval algebra bridge for the `Q0`-minor residual.

This is the minor-arc companion to `Q0MajorTailTTStarAlgebra`. It provides the deterministic
bookkeeping needed before any SSU / Type-I estimates are attempted:

* the hard minor weight and its Fourier coefficients;
* the complement identities against the existing major-arc Fourier weight;
* the finite `(n,m)` expansion of the `Q0`-minor inner integral;
* the outer `β`-kernel collapse to explicit kernel coefficients.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep16CircleToInterval
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The hard `Q0` minor-arc weight as a `ℂ`-valued function on `α ∈ ℝ`. -/
noncomputable def minorArcWeightC (X : ℕ) (Δ : ℝ) : ℝ → ℂ :=
  (majorArcSetQ0 X Δ)ᶜ.indicator (fun _ : ℝ => (1 : ℂ))

/-- The `α`-Fourier coefficient of the hard minor-arc indicator weight. -/
noncomputable def minorArcWeightFourier (X : ℕ) (Δ : ℝ) (t : ℤ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ), minorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)

/-- The `α`-integral appearing in the `Q0`-minor piece of the correlation integral. -/
noncomputable def innerMinorQ0 (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ), minorArcWeightC X Δ α * innerIntegrand X N β α

/-- Kernel coefficient alias with the `k = m - n` convention used by the minor TT* split. -/
abbrev KHatH (k : ℤ) : ℂ :=
  coeffC (-k)

private lemma intervalIntegrable_fourier_int (t : ℤ) :
    IntervalIntegrable (fun α : ℝ => (fourier (T := (1 : ℝ)) t (α : UC) : ℂ))
      volume (0 : ℝ) (1 : ℝ) := by
  have hcont : Continuous fun α : ℝ => (fourier (T := (1 : ℝ)) t (α : UC) : ℂ) := by
    fun_prop
  exact hcont.intervalIntegrable (μ := volume) (0 : ℝ) (1 : ℝ)

private lemma minorArcWeightFourier_eq_indicator (X : ℕ) (Δ : ℝ) (t : ℤ) :
    minorArcWeightFourier X Δ t
      =
    ∫ α in (0 : ℝ)..(1 : ℝ),
      (majorArcSetQ0 X Δ)ᶜ.indicator
        (fun a : ℝ => (fourier (T := (1 : ℝ)) t (a : UC) : ℂ)) α := by
  classical
  unfold minorArcWeightFourier minorArcWeightC
  refine congrArg (fun f : ℝ → ℂ => ∫ α in (0 : ℝ)..(1 : ℝ), f α) ?_
  funext α
  by_cases hα : α ∈ (majorArcSetQ0 X Δ)ᶜ
  · simp [hα]
  · simp [hα]

private lemma intervalIntegrable_majorArcWeight_mul_fourier (X : ℕ) (Δ : ℝ) (t : ℤ) :
    IntervalIntegrable
      (fun α : ℝ =>
        majorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ))
      volume (0 : ℝ) (1 : ℝ) := by
  have hbase := intervalIntegrable_fourier_int (t := t)
  have hs : MeasurableSet (majorArcSetQ0 X Δ) := majorArcSetQ0_measurableSet (X := X) (Δ := Δ)
  have hind :
      IntervalIntegrable
        ((majorArcSetQ0 X Δ).indicator
          (fun α : ℝ => (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)))
        volume (0 : ℝ) (1 : ℝ) :=
    Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
      (s := majorArcSetQ0 X Δ) (hs := hs)
      (f := fun α : ℝ => (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)) hbase
  refine hind.congr ?_
  intro α hα
  by_cases hmem : α ∈ majorArcSetQ0 X Δ
  · simp [Q0MajorTailTTStarAlgebra.majorArcWeightC, hmem]
  · simp [Q0MajorTailTTStarAlgebra.majorArcWeightC, hmem]

private lemma intervalIntegrable_minorArcWeight_mul_fourier (X : ℕ) (Δ : ℝ) (t : ℤ) :
    IntervalIntegrable
      (fun α : ℝ =>
        minorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ))
      volume (0 : ℝ) (1 : ℝ) := by
  have hbase := intervalIntegrable_fourier_int (t := t)
  have hs : MeasurableSet (majorArcSetQ0 X Δ) := majorArcSetQ0_measurableSet (X := X) (Δ := Δ)
  have hind :
      IntervalIntegrable
        ((majorArcSetQ0 X Δ)ᶜ.indicator
          (fun α : ℝ => (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)))
        volume (0 : ℝ) (1 : ℝ) :=
    Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
      (s := (majorArcSetQ0 X Δ)ᶜ) (hs := hs.compl)
      (f := fun α : ℝ => (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)) hbase
  refine hind.congr ?_
  intro α hα
  by_cases hmem : α ∈ (majorArcSetQ0 X Δ)ᶜ
  · simp [minorArcWeightC, hmem]
  · simp [minorArcWeightC, hmem]

private lemma intervalIntegral_zero_one_fourier_eq (n : ℤ) :
    (∫ β in (0 : ℝ)..(1 : ℝ), (fourier (T := (1 : ℝ)) n (β : UC) : ℂ))
      =
    (if n = 0 then 1 else 0) := by
  have h1 :
      (∫ β in (0 : ℝ)..(1 : ℝ), (fourier (T := (1 : ℝ)) n (β : UC) : ℂ))
        =
      ∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ) := by
    simpa using (AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (t := (0 : ℝ))
      (f := fun β : UC => (fourier (T := (1 : ℝ)) n β : ℂ)))
  have hvol_haar :
      (∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ))
        =
      (∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ) ∂μ) := by
    simpa [μ] using
      (AddCircle.integral_haarAddCircle (T := (1 : ℝ))
        (f := fun β : UC => (fourier (T := (1 : ℝ)) n β : ℂ))).symm
  calc
    (∫ β in (0 : ℝ)..(1 : ℝ), (fourier (T := (1 : ℝ)) n (β : UC) : ℂ))
        = ∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ) := h1
    _ = (∫ β : UC, (fourier (T := (1 : ℝ)) n β : ℂ) ∂μ) := hvol_haar
    _ = (if n = 0 then 1 else 0) := by
        simpa using (Goldbach.Cert.MajorArcStep7FourierOrthogonality.integral_fourier (n := n))

theorem minorArcWeightFourier_eq_full_sub_majorArcWeightFourier
    (X : ℕ) (Δ : ℝ) (t : ℤ) :
    minorArcWeightFourier X Δ t
      =
    (if t = 0 then 1 else 0)
      - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ t := by
  have hsum :
      minorArcWeightFourier X Δ t
        + Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ t
        =
      ∫ α in (0 : ℝ)..(1 : ℝ), (fourier (T := (1 : ℝ)) t (α : UC) : ℂ) := by
    have hadd :
        (∫ α in (0 : ℝ)..(1 : ℝ),
            minorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)
              +
            (Q0MajorTailTTStarAlgebra.majorArcWeightC X Δ α
              * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)))
          =
        minorArcWeightFourier X Δ t
          + Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ t := by
      simpa [minorArcWeightFourier, Q0MajorTailTTStarAlgebra.majorArcWeightFourier] using
        (intervalIntegral.integral_add
          (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun α : ℝ =>
            minorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ))
          (g := fun α : ℝ =>
            Q0MajorTailTTStarAlgebra.majorArcWeightC X Δ α
              * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ))
          (intervalIntegrable_minorArcWeight_mul_fourier (X := X) (Δ := Δ) (t := t))
          (intervalIntegrable_majorArcWeight_mul_fourier (X := X) (Δ := Δ) (t := t)))
    calc
      minorArcWeightFourier X Δ t
          + Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ t
        =
      ∫ α in (0 : ℝ)..(1 : ℝ),
        minorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)
          +
        (Q0MajorTailTTStarAlgebra.majorArcWeightC X Δ α
          * (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)) := by
            simpa using hadd.symm
      _ =
      ∫ α in (0 : ℝ)..(1 : ℝ), (fourier (T := (1 : ℝ)) t (α : UC) : ℂ) := by
        apply intervalIntegral.integral_congr_ae
        refine Filter.Eventually.of_forall ?_
        intro α _hα
        by_cases hα : α ∈ majorArcSetQ0 X Δ
        · simp [minorArcWeightC, Q0MajorTailTTStarAlgebra.majorArcWeightC, hα]
        · have hαc : α ∈ (majorArcSetQ0 X Δ)ᶜ := hα
          simp [minorArcWeightC, Q0MajorTailTTStarAlgebra.majorArcWeightC, hα, hαc]
  calc
    minorArcWeightFourier X Δ t
        =
      (minorArcWeightFourier X Δ t
        + Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ t)
        - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ t := by ring
    _ =
      (∫ α in (0 : ℝ)..(1 : ℝ), (fourier (T := (1 : ℝ)) t (α : UC) : ℂ))
        - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ t := by rw [hsum]
    _ =
      (if t = 0 then 1 else 0)
        - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ t := by
          rw [intervalIntegral_zero_one_fourier_eq]

theorem minorArcWeightFourier_zero
    (X : ℕ) (Δ : ℝ) :
    minorArcWeightFourier X Δ 0
      =
    1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ 0 := by
  simpa using minorArcWeightFourier_eq_full_sub_majorArcWeightFourier (X := X) (Δ := Δ) (t := 0)

theorem minorArcWeightFourier_ne_zero
    (X : ℕ) (Δ : ℝ) {t : ℤ} (ht : t ≠ 0) :
    minorArcWeightFourier X Δ t
      =
    -Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ t := by
  have h :=
    minorArcWeightFourier_eq_full_sub_majorArcWeightFourier (X := X) (Δ := Δ) (t := t)
  simpa [ht] using h

theorem corr_integral_minor_Q0_eq_kernel_mul_innerMinorQ0 (X N : ℕ) (Δ : ℝ) :
    corr_integral_minor_Q0 X N Δ
      =
    ∫ β in (0 : ℝ)..(1 : ℝ), kernelPolyC (β : UC) * innerMinorQ0 X N Δ β := by
  unfold corr_integral_minor_Q0 innerMinorQ0 minorArcWeightC
  refine congrArg (fun f : ℝ → ℂ => ∫ β in (0 : ℝ)..(1 : ℝ), kernelPolyC (β : UC) * f β) ?_
  funext β
  refine congrArg (fun f : ℝ → ℂ => ∫ α in (0 : ℝ)..(1 : ℝ), f α) ?_
  funext α
  by_cases hα : α ∈ (majorArcSetQ0 X Δ)ᶜ
  · simp [hα]
  · simp [hα]

private lemma expSum_sub_eq_sum_mul (X N : ℕ) (α β : UC) :
    expSum X N (α - β)
      =
    ∑ n ∈ s N,
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ) := by
  classical
  unfold expSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hchar :=
    MajorArcStep12ShiftedExpSums.fourier_mul_fourier_neg_eq_sub
      (n := (n : ℤ)) (α := α) (β := β)
  calc
    aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) (α - β) : ℂ)
        =
      aTerm X n
        * ((fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)) := by
          simpa [mul_assoc] using congrArg (fun z : ℂ => aTerm X n * z) hchar.symm
    _ =
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ) := by
          ring

private lemma expSum_add_eq_sum_mul (X N : ℕ) (α β : UC) :
    expSum X N (α + β)
      =
    ∑ n ∈ s N,
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
        * (fourier (T := (1 : ℝ)) (n : ℤ) β : ℂ) := by
  classical
  unfold expSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hchar :=
    MajorArcStep12ShiftedExpSums.fourier_mul_fourier_eq_add
      (n := (n : ℤ)) (α := α) (β := β)
  calc
    aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) (α + β) : ℂ)
        =
      aTerm X n
        * ((fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (n : ℤ) β : ℂ)) := by
          simpa [mul_assoc] using congrArg (fun z : ℂ => aTerm X n * z) hchar.symm
    _ =
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
        * (fourier (T := (1 : ℝ)) (n : ℤ) β : ℂ) := by
          ring

private lemma fourier_mul_fourier_mul_fourier (n m N : ℤ) (α : UC) :
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
        * (fourier (T := (1 : ℝ)) n α : ℂ)
        * (fourier (T := (1 : ℝ)) m α : ℂ)
      =
    (fourier (T := (1 : ℝ)) (n + m - N) α : ℂ) := by
  have hnm :
      (fourier (T := (1 : ℝ)) (n + m) α : ℂ)
        =
      (fourier (T := (1 : ℝ)) n α : ℂ) * (fourier (T := (1 : ℝ)) m α : ℂ) := by
    simpa using (fourier_add (T := (1 : ℝ)) (m := n) (n := m) (x := α))
  have hsub : (n + m - N) = (n + m) + (-N) := by ring
  calc
    (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
        * (fourier (T := (1 : ℝ)) n α : ℂ)
        * (fourier (T := (1 : ℝ)) m α : ℂ)
        =
      (fourier (T := (1 : ℝ)) n α : ℂ)
        * (fourier (T := (1 : ℝ)) m α : ℂ)
        * (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) := by
          ring
    _ = (fourier (T := (1 : ℝ)) (n + m) α : ℂ) * (fourier (T := (1 : ℝ)) (-N) α : ℂ) := by
          simp [hnm, mul_assoc]
    _ = (fourier (T := (1 : ℝ)) ((n + m) + (-N)) α : ℂ) := by
          simpa [fourier_add (T := (1 : ℝ)) (m := (n + m)) (n := (-N)) (x := α), mul_assoc]
    _ = (fourier (T := (1 : ℝ)) (n + m - N) α : ℂ) := by
          simpa [hsub]

private lemma fourier_mul_fourier_neg_eq_sub_freq (n m : ℤ) (β : UC) :
    (fourier (T := (1 : ℝ)) m β : ℂ) * (fourier (T := (1 : ℝ)) (-n) β : ℂ)
      =
    (fourier (T := (1 : ℝ)) (m - n) β : ℂ) := by
  have h : (m - n) = m + (-n) := by ring
  simpa [h, fourier_add (T := (1 : ℝ)) (m := m) (n := (-n)) (x := β), mul_assoc]

theorem innerMinorQ0_eq_sum_nm
    (X N : ℕ) (Δ : ℝ) (β : ℝ) :
    innerMinorQ0 X N Δ β
      =
    ∑ n ∈ s N, ∑ m ∈ s N,
      aTerm X n * aTerm X m
        * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
        * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
  classical
  rw [innerMinorQ0]
  have hsub (α : ℝ) :
      expSum X N ((α : UC) - (β : UC))
        =
      ∑ n ∈ s N,
        aTerm X n
          * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ) := by
    simpa using expSum_sub_eq_sum_mul (X := X) (N := N) (α := (α : UC)) (β := (β : UC))
  have hadd (α : ℝ) :
      expSum X N ((α : UC) + (β : UC))
        =
      ∑ n ∈ s N,
        aTerm X n
          * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
          * (fourier (T := (1 : ℝ)) (n : ℤ) (β : UC) : ℂ) := by
    simpa using expSum_add_eq_sum_mul (X := X) (N := N) (α := (α : UC)) (β := (β : UC))
  have hpoint :
      (fun α : ℝ =>
          minorArcWeightC X Δ α * innerIntegrand X N β α)
        =
      fun α : ℝ =>
        ∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * (minorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
    funext α
    unfold innerIntegrand
    rw [hsub α, hadd α]
    let f : ℕ → ℂ := fun n =>
      aTerm X n
        * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ)
    let g : ℕ → ℂ := fun m =>
      aTerm X m
        * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)
        * (fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ)
    have hprod :
        (∑ n ∈ s N, f n) * (∑ m ∈ s N, g m) =
          ∑ n ∈ s N, ∑ m ∈ s N, f n * g m := by
      simpa [f, g] using
        (Finset.sum_mul_sum (s := s N) (t := s N) (f := f) (g := g))
    have hdist :
        minorArcWeightC X Δ α
            * (((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * (∑ n ∈ s N, f n))
                * (∑ m ∈ s N, g m))
          =
        ∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * (minorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
      have :
          ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * (∑ n ∈ s N, f n))
              * (∑ m ∈ s N, g m)
            =
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ) * ((∑ n ∈ s N, f n) * (∑ m ∈ s N, g m)) := by
        ring
      rw [this, hprod]
      calc
        minorArcWeightC X Δ α
            * ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                * (∑ n ∈ s N, ∑ m ∈ s N, f n * g m))
            =
          (minorArcWeightC X Δ α
              * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
            * (∑ n ∈ s N, ∑ m ∈ s N, f n * g m) := by
              simp [mul_assoc]
        _ =
          ∑ n ∈ s N,
            (minorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
              * (∑ m ∈ s N, f n * g m) := by
              simp only [Finset.mul_sum]
        _ =
          ∑ n ∈ s N, ∑ m ∈ s N,
            (minorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
              * (f n * g m) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simp only [Finset.mul_sum]
        _ =
          ∑ n ∈ s N, ∑ m ∈ s N,
            aTerm X n * aTerm X m
              * (minorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hβ :
                  (fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ)
                      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ)
                    =
                  (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using
                  (fourier_mul_fourier_neg_eq_sub_freq (n := (n : ℤ)) (m := (m : ℤ)) (β := (β : UC)))
              have hα :
                  (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                      * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
                      * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)
                    =
                  (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ) := by
                simpa using
                  (fourier_mul_fourier_mul_fourier
                    (n := (n : ℤ)) (m := (m : ℤ)) (N := (N : ℤ)) (α := (α : UC)))
              have :
                  (minorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
                      * (f n * g m)
                    =
                  aTerm X n * aTerm X m
                    * (minorArcWeightC X Δ α
                        * ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                            * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
                            * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)))
                    * ((fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ)
                        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ)) := by
                simp only [f, g]
                ring
              calc
                (minorArcWeightC X Δ α
                      * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ))
                    * (f n * g m)
                    =
                  aTerm X n * aTerm X m
                    * (minorArcWeightC X Δ α
                        * ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                            * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
                            * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)))
                    * ((fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ)
                        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ)) := this
                _ =
                  aTerm X n * aTerm X m
                    * (minorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
                      simp only [hα, hβ]
    have hf :
        (∑ n ∈ s N,
            aTerm X n
              * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
              * (fourier (T := (1 : ℝ)) (-(n : ℤ)) (β : UC) : ℂ))
          =
        ∑ n ∈ s N, f n := by
      rfl
    have hg :
        (∑ m ∈ s N,
            aTerm X m
              * (fourier (T := (1 : ℝ)) (m : ℤ) (α : UC) : ℂ)
              * (fourier (T := (1 : ℝ)) (m : ℤ) (β : UC) : ℂ))
          =
        ∑ m ∈ s N, g m := by
      rfl
    rw [hf, hg]
    exact hdist
  have hInt_nm :
      ∀ n ∈ s N, ∀ m ∈ s N,
        IntervalIntegrable
          (fun α : ℝ =>
            aTerm X n * aTerm X m
              * (minorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
          volume (0 : ℝ) (1 : ℝ) := by
    intro n hn m hm
    have hcont :
        Continuous fun α : ℝ =>
          (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ) := by
      fun_prop
    have hbase :
        IntervalIntegrable
          (fun α : ℝ =>
            (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
          volume (0 : ℝ) (1 : ℝ) :=
      hcont.intervalIntegrable (μ := volume) (0 : ℝ) (1 : ℝ)
    have hs : MeasurableSet ((majorArcSetQ0 X Δ)ᶜ) :=
      (majorArcSetQ0_measurableSet (X := X) (Δ := Δ)).compl
    have hind :
        IntervalIntegrable
          (((majorArcSetQ0 X Δ)ᶜ).indicator
            (fun α : ℝ =>
              (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)))
          volume (0 : ℝ) (1 : ℝ) :=
      Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
        (s := (majorArcSetQ0 X Δ)ᶜ) (hs := hs)
        (f := fun α : ℝ =>
          (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) hbase
    have hrew :
        (fun α : ℝ =>
            aTerm X n * aTerm X m
              * (minorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
          =
        fun α : ℝ =>
          (aTerm X n * aTerm X m * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
            *
          (((majorArcSetQ0 X Δ)ᶜ).indicator
            (fun α : ℝ =>
              (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) α) := by
      funext α
      by_cases hα : α ∈ (majorArcSetQ0 X Δ)ᶜ
      · simp only [minorArcWeightC, hα, Set.indicator_of_mem, mul_assoc, mul_left_comm, mul_comm,
          one_mul, mul_one]
      · simp [minorArcWeightC, Set.indicator_of_notMem, hα, mul_assoc, mul_left_comm, mul_comm]
    have :
        IntervalIntegrable
          (fun α : ℝ =>
            (aTerm X n * aTerm X m * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
              *
            (((majorArcSetQ0 X Δ)ᶜ).indicator
              (fun α : ℝ =>
                (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) α))
          volume (0 : ℝ) (1 : ℝ) := by
      exact hind.const_mul
        (aTerm X n * aTerm X m * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
    refine this.congr ?_
    intro α hα
    simpa using congrArg (fun f : ℝ → ℂ => f α) hrew.symm
  have hswap_n :
      (∫ α in (0 : ℝ)..(1 : ℝ),
          ∑ n ∈ s N, ∑ m ∈ s N,
            aTerm X n * aTerm X m
              * (minorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
        =
      ∑ n ∈ s N, ∑ m ∈ s N,
        ∫ α in (0 : ℝ)..(1 : ℝ),
          aTerm X n * aTerm X m
            * (minorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
    have houter :
        ∀ n ∈ s N,
          IntervalIntegrable
            (fun α : ℝ =>
              ∑ m ∈ s N,
                aTerm X n * aTerm X m
                  * (minorArcWeightC X Δ α
                    * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
            volume (0 : ℝ) (1 : ℝ) := by
      intro n hn
      classical
      have :=
        IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (s := s N)
          (f := fun m : ℕ => fun α : ℝ =>
            aTerm X n * aTerm X m
              * (minorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
          (fun m hm => hInt_nm n hn m hm)
      have hfun :
          (∑ m ∈ s N, fun α : ℝ =>
              aTerm X n * aTerm X m
                * (minorArcWeightC X Δ α
                    * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
            =
          (fun α : ℝ =>
            ∑ m ∈ s N,
              aTerm X n * aTerm X m
                * (minorArcWeightC X Δ α
                    * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
        funext α
        simp only [Finset.sum_apply]
      refine this.congr ?_
      intro α hα
      simpa using congrArg (fun f : ℝ → ℂ => f α) hfun
    have h1 :=
      intervalIntegral.integral_finset_sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (s := s N)
        (f := fun n : ℕ => fun α : ℝ =>
          ∑ m ∈ s N,
            aTerm X n * aTerm X m
              * (minorArcWeightC X Δ α
                  * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
        houter
    refine h1.trans ?_
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hinner :=
      intervalIntegral.integral_finset_sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (s := s N)
        (f := fun m : ℕ => fun α : ℝ =>
          aTerm X n * aTerm X m
            * (minorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
        (fun m hm => hInt_nm n hn m hm)
    simpa using hinner
  calc
    (∫ α in (0 : ℝ)..(1 : ℝ), minorArcWeightC X Δ α * innerIntegrand X N β α)
        =
      ∫ α in (0 : ℝ)..(1 : ℝ),
        ∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * (minorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
          exact congrArg (fun f : ℝ → ℂ => ∫ α in (0 : ℝ)..(1 : ℝ), f α) hpoint
    _ =
      ∑ n ∈ s N, ∑ m ∈ s N,
        ∫ α in (0 : ℝ)..(1 : ℝ),
          aTerm X n * aTerm X m
            * (minorArcWeightC X Δ α
                * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
            * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
          exact hswap_n
    _ =
      ∑ n ∈ s N, ∑ m ∈ s N,
        aTerm X n * aTerm X m
          * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
          * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          refine Finset.sum_congr rfl ?_
          intro m hm
          have hconst :
              (∫ α in (0 : ℝ)..(1 : ℝ),
                  aTerm X n * aTerm X m
                    * (minorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
                =
              aTerm X n * aTerm X m
                * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ) := by
            let c : ℂ := aTerm X n * aTerm X m
              * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)
            calc
              (∫ α in (0 : ℝ)..(1 : ℝ),
                  aTerm X n * aTerm X m
                    * (minorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
                  =
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  c
                    * (minorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ))) := by
                  exact congrArg (fun f : ℝ → ℂ => ∫ α in (0 : ℝ)..(1 : ℝ), f α) <| by
                    funext α
                    simp [c, mul_assoc, mul_left_comm, mul_comm]
              _ =
                c
                  * (∫ α in (0 : ℝ)..(1 : ℝ),
                    minorArcWeightC X Δ α
                      * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)) := by
                  exact (intervalIntegral.integral_const_mul
                    (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) c
                    (fun α : ℝ =>
                      minorArcWeightC X Δ α
                        * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) - (N : ℤ)) (α : UC) : ℂ)))
              _ = _ := by
                  simp [minorArcWeightFourier, c, mul_assoc, mul_left_comm, mul_comm]
          simpa [mul_assoc, mul_left_comm, mul_comm] using hconst

private lemma continuous_kernelPoly_real : Continuous fun β : ℝ => kernelPolyC (β : UC) := by
  dsimp [kernelPolyC]
  have :
      Continuous fun β : ℝ =>
        ∑ k ∈ Goldbach.BG_Identity.S_BG,
          (Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k (β : UC) := by
    refine continuous_finset_sum _ ?_
    intro j _hj
    exact continuous_const.mul (((fourier (T := (1 : ℝ)) j).continuous).comp
      (AddCircle.continuous_mk' (1 : ℝ)))
  simpa [Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly_eq] using this

private lemma intervalIntegrable_kernelPoly_mul_fourier (k : ℤ) :
    IntervalIntegrable
      (fun β : ℝ => kernelPolyC (β : UC) * (fourier (T := (1 : ℝ)) k (β : UC) : ℂ))
      volume (0 : ℝ) (1 : ℝ) := by
  have hcont :
      Continuous fun β : ℝ =>
        kernelPolyC (β : UC) * (fourier (T := (1 : ℝ)) k (β : UC) : ℂ) := by
    exact continuous_kernelPoly_real.mul <| by
      fun_prop
  exact hcont.intervalIntegrable (μ := volume) (0 : ℝ) (1 : ℝ)

private lemma intervalIntegral_kernelPoly_mul_fourier_neg_eq_coeffC (k : ℤ) :
    (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) * (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ))
      =
    coeffC k := by
  have h1 :
      (∫ β in (0 : ℝ)..(1 : ℝ),
          kernelPolyC (β : UC) * (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ))
        =
      ∫ β : UC, kernelPolyC β * (fourier (T := (1 : ℝ)) (-k) β : ℂ) := by
    simpa using
      (AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (t := (0 : ℝ))
        (f := fun β : UC =>
          kernelPolyC β * (fourier (T := (1 : ℝ)) (-k) β : ℂ)))
  have hvol_haar :
      (∫ β : UC, kernelPolyC β * (fourier (T := (1 : ℝ)) (-k) β : ℂ))
        =
      (∫ β : UC, kernelPolyC β * (fourier (T := (1 : ℝ)) (-k) β : ℂ) ∂μ) := by
    simpa [μ] using
      (AddCircle.integral_haarAddCircle (T := (1 : ℝ))
        (f := fun β : UC =>
          kernelPolyC β * (fourier (T := (1 : ℝ)) (-k) β : ℂ))).symm
  calc
    (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) * (fourier (T := (1 : ℝ)) (-k) (β : UC) : ℂ))
        =
      ∫ β : UC, kernelPolyC β * (fourier (T := (1 : ℝ)) (-k) β : ℂ) := h1
    _ =
      (∫ β : UC, kernelPolyC β * (fourier (T := (1 : ℝ)) (-k) β : ℂ) ∂μ) := hvol_haar
    _ = coeffC k := by
        simpa [coeffC, kernelPolyC] using
          (Goldbach.Cert.MajorArcStep9CorrelationIntegral.integral_kernelPoly_mul_fourier_neg
            (k := k))

theorem corr_integral_minor_Q0_eq_sum_nm
    (X N : ℕ) (Δ : ℝ) :
    corr_integral_minor_Q0 X N Δ
      =
    ∑ n ∈ s N, ∑ m ∈ s N,
      aTerm X n * aTerm X m
        * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
        * coeffC ((n : ℤ) - (m : ℤ)) := by
  classical
  rw [corr_integral_minor_Q0_eq_kernel_mul_innerMinorQ0]
  have hrewrite :
      (fun β : ℝ => kernelPolyC (β : UC) * innerMinorQ0 X N Δ β)
        =
      fun β : ℝ =>
        kernelPolyC (β : UC)
          * (∑ n ∈ s N, ∑ m ∈ s N,
              aTerm X n * aTerm X m
                * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
    funext β
    simpa using congrArg (fun z : ℂ => kernelPolyC (β : UC) * z)
      (innerMinorQ0_eq_sum_nm (X := X) (N := N) (Δ := Δ) (β := β))
  have hInt :
      (∫ β in (0 : ℝ)..(1 : ℝ), kernelPolyC (β : UC) * innerMinorQ0 X N Δ β)
        =
      ∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC)
          * (∑ n ∈ s N, ∑ m ∈ s N,
              aTerm X n * aTerm X m
                * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
    exact congrArg (fun f : ℝ → ℂ => ∫ β in (0 : ℝ)..(1 : ℝ), f β) hrewrite
  rw [hInt]
  have hInt_nm :
      ∀ n ∈ s N, ∀ m ∈ s N,
        IntervalIntegrable
          (fun β : ℝ =>
            kernelPolyC (β : UC)
              * (aTerm X n * aTerm X m
                  * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          volume (0 : ℝ) (1 : ℝ) := by
    intro n hn m hm
    have hcont :
        Continuous fun β : ℝ =>
          kernelPolyC (β : UC)
            * (aTerm X n * aTerm X m
                * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
      exact continuous_kernelPoly_real.mul <| by
        refine continuous_const.mul ?_
        fun_prop
    exact hcont.intervalIntegrable (μ := volume) (0 : ℝ) (1 : ℝ)
  have houter :
      ∀ n ∈ s N,
        IntervalIntegrable
          (fun β : ℝ =>
            ∑ m ∈ s N,
              kernelPolyC (β : UC)
                * (aTerm X n * aTerm X m
                    * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          volume (0 : ℝ) (1 : ℝ) := by
    intro n hn
    have :=
      IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (s := s N)
        (f := fun m : ℕ => fun β : ℝ =>
          kernelPolyC (β : UC)
            * (aTerm X n * aTerm X m
                * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
        (fun m hm => hInt_nm n hn m hm)
    have hfun :
        (∑ m ∈ s N, fun β : ℝ =>
            kernelPolyC (β : UC)
              * (aTerm X n * aTerm X m
                  * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          =
        (fun β : ℝ =>
          ∑ m ∈ s N,
            kernelPolyC (β : UC)
              * (aTerm X n * aTerm X m
                  * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))) := by
      funext β
      simp only [Finset.sum_apply]
    refine this.congr ?_
    intro β hβ
    simpa using congrArg (fun f : ℝ → ℂ => f β) hfun
  calc
    (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC)
          * (∑ n ∈ s N, ∑ m ∈ s N,
              aTerm X n * aTerm X m
                * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
        =
      ∑ n ∈ s N,
        ∫ β in (0 : ℝ)..(1 : ℝ),
          ∑ m ∈ s N,
            kernelPolyC (β : UC)
              * (aTerm X n * aTerm X m
                  * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                  * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
          simpa [Finset.mul_sum, mul_assoc] using
            (intervalIntegral.integral_finset_sum
              (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
              (s := s N)
              (f := fun n β =>
                ∑ m ∈ s N,
                  kernelPolyC (β : UC)
                    * (aTerm X n * aTerm X m
                        * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                        * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
              houter)
    _ =
      ∑ n ∈ s N, ∑ m ∈ s N,
        ∫ β in (0 : ℝ)..(1 : ℝ),
          kernelPolyC (β : UC)
            * (aTerm X n * aTerm X m
                * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simpa using
            (intervalIntegral.integral_finset_sum
              (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
              (s := s N)
              (f := fun m β =>
                kernelPolyC (β : UC)
                  * (aTerm X n * aTerm X m
                      * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
              (fun m hm => hInt_nm n hn m hm))
    _ =
      ∑ n ∈ s N, ∑ m ∈ s N,
        aTerm X n * aTerm X m
          * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
          * coeffC ((n : ℤ) - (m : ℤ)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          refine Finset.sum_congr rfl ?_
          intro m hm
          let c : ℂ :=
            aTerm X n * aTerm X m * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
          have hconst :
              (∫ β in (0 : ℝ)..(1 : ℝ),
                  kernelPolyC (β : UC)
                    * (aTerm X n * aTerm X m
                        * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                        * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
                =
              c
                * (∫ β in (0 : ℝ)..(1 : ℝ),
                    kernelPolyC (β : UC)
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
            calc
              (∫ β in (0 : ℝ)..(1 : ℝ),
                  kernelPolyC (β : UC)
                    * (aTerm X n * aTerm X m
                        * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                        * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
                  =
                (∫ β in (0 : ℝ)..(1 : ℝ),
                  c
                    * (kernelPolyC (β : UC)
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))) := by
                    exact congrArg (fun f : ℝ → ℂ => ∫ β in (0 : ℝ)..(1 : ℝ), f β) <| by
                      funext β
                      simp [c, mul_assoc, mul_left_comm, mul_comm]
              _ =
                c
                  * (∫ β in (0 : ℝ)..(1 : ℝ),
                    kernelPolyC (β : UC)
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := by
                    exact (intervalIntegral.integral_const_mul
                      (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) c
                      (fun β : ℝ =>
                        kernelPolyC (β : UC)
                          * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
          have hkernel :
              (∫ β in (0 : ℝ)..(1 : ℝ),
                  kernelPolyC (β : UC)
                    * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ))
                =
              coeffC ((n : ℤ) - (m : ℤ)) := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              intervalIntegral_kernelPoly_mul_fourier_neg_eq_coeffC ((n : ℤ) - (m : ℤ))
          calc
            (∫ β in (0 : ℝ)..(1 : ℝ),
                kernelPolyC (β : UC)
                  * (aTerm X n * aTerm X m
                      * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                      * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)))
                = c
                  * (∫ β in (0 : ℝ)..(1 : ℝ),
                      kernelPolyC (β : UC)
                        * (fourier (T := (1 : ℝ)) ((m : ℤ) - (n : ℤ)) (β : UC) : ℂ)) := hconst
            _ = c * coeffC ((n : ℤ) - (m : ℤ)) := by rw [hkernel]
            _ =
              aTerm X n * aTerm X m
                * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
                * coeffC ((n : ℤ) - (m : ℤ)) := by
                  simp [c, mul_assoc, mul_left_comm, mul_comm]

theorem corr_integral_minor_Q0_eq_sum_nm_kHatH
    (X N : ℕ) (Δ : ℝ) :
    corr_integral_minor_Q0 X N Δ
      =
    ∑ n ∈ s N, ∑ m ∈ s N,
      aTerm X n * aTerm X m
        * minorArcWeightFourier X Δ ((n : ℤ) + (m : ℤ) - (N : ℤ))
        * KHatH ((m : ℤ) - (n : ℤ)) := by
  rw [corr_integral_minor_Q0_eq_sum_nm (X := X) (N := N) (Δ := Δ)]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro m hm
  simp [KHatH]

theorem minorResidual_eq_q0NormFactor_mul_sum_nm
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    minorResidual X N Δ_canon
      =
    q0NormFactor N
      * (∑ n ∈ s N, ∑ m ∈ s N,
          aTerm X n * aTerm X m
            * minorArcWeightFourier X Δ_canon ((n : ℤ) + (m : ℤ) - (N : ℤ))
            * KHatH ((m : ℤ) - (n : ℤ))) := by
  rw [minorResidual_eq_norm_mul_minor_Q0
    (X := X) (N := N) (Δ := Δ_canon)
    (hInner := hInner (X := X) (N := N) hX hN)
    (hOuterMaj := hOuterMaj (X := X) (N := N) hX hN Δ_canon)
    (hOuterMin := hOuterMin (X := X) (N := N) hX hN Δ_canon)]
  rw [corr_integral_minor_Q0_eq_sum_nm_kHatH (X := X) (N := N) (Δ := Δ_canon)]

end

end Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
