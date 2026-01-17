import Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
import Goldbach.Cert.MajorArcModules.Q0MajorTailConstModeBound
import Goldbach.Cert.MajorArcStep9CorrelationIntegral
import Goldbach.Cert.MajorArcStep16CircleToInterval
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Algebra.Star.BigOperators
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
Deterministic bounds for the `h = 0` remainder term in the option-3 ε₂-large plan.

This file provides:

* an explicit Fourier-series description of `innerFull X N β` as a (finite) Fourier polynomial
  in `β`, coming from Fourier orthogonality in the `α` variable; and
* a corresponding `L²` bound in `β` (via orthogonality of characters), suitable for budgeting the
  mean-zero decomposition remainder
  `innerMajorQ0Remainder X N Δ β = (majorArcConstMode X Δ) * innerFull X N β`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero

open scoped BigOperators Interval
open scoped ComplexConjugate
open scoped InnerProductSpace

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep9CorrelationIntegral
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep16CircleToInterval
open Goldbach.Cert.MajorArcStep17MajorMinorSplit

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private abbrev aβ : ℝ := (-( (2 : ℝ)⁻¹) : ℝ)
private abbrev bβ : ℝ := ((2 : ℝ)⁻¹ : ℝ)
private abbrev Iβ : Set ℝ := Set.Ioc aβ bβ

private lemma hab : aβ < bβ := by
  norm_num [aβ, bβ]

private lemma bβ_eq_aβ_add_one : bβ = aβ + 1 := by
  norm_num [aβ, bβ]

private lemma mem_s_sub_of_mem_s {N n : ℕ} (hn : n ∈ s N) : N - n ∈ s N := by
  -- copied (non-private) from the Step 10 bookkeeping lemma
  rcases Finset.mem_Icc.mp hn with ⟨hn2, hnN⟩
  have hn_le : n ≤ N := le_trans hnN (Nat.sub_le N 2)
  have h2N : 2 ≤ N := le_trans hn2 hn_le
  have hNp2_le : n + 2 ≤ N := (Nat.le_sub_iff_add_le h2N).1 hnN
  have h2pN : 2 + n ≤ N := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hNp2_le
  have hNm_ge2 : 2 ≤ N - n := (Nat.le_sub_iff_add_le hn_le).2 h2pN
  have hNm_le : N - n ≤ N - 2 := Nat.sub_le_sub_left hn2 N
  exact Finset.mem_Icc.mpr ⟨hNm_ge2, hNm_le⟩

private lemma abs_BG_Lambda_le_log
    {N n : ℕ} (hN : 2 ≤ N) (hn : n ∈ s N) :
    |Goldbach.BG_Bank.Λ n| ≤ Real.log (N : ℝ) := by
  -- `Λ n` is `log n` if `n` is prime, else `0`.
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
  have hn_pos : 0 < (n : ℝ) := by
    have : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn2
    exact_mod_cast this
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
    have h1N' : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) hN
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1N'
    exact Real.log_nonneg h1N
  unfold Goldbach.BG_Bank.Λ
  by_cases hp : Nat.Prime n
  · -- `|log n| = log n ≤ log N`
    have hn_le' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn_le
    have hlog_le : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hn_pos hn_le'
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have h1n' : (1 : ℕ) ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hn2
      have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1n'
      exact Real.log_nonneg h1n
    simpa [hp, abs_of_nonneg hlog_nonneg] using hlog_le
  · -- `Λ n = 0`
    simpa [hp, abs_of_nonneg hlogN_nonneg]

/-!
## `innerFull` as a Fourier polynomial in `β`
-/

private noncomputable def innerFullUC (X N : ℕ) (β : UC) : ℂ :=
  ∫ α : UC, (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * expSum X N (α - β) * expSum X N (α + β) ∂μ

private lemma innerFull_eq_innerFullUC (X N : ℕ) (β : ℝ) :
    innerFull X N β = innerFullUC X N (β : UC) := by
  -- Convert the `α`-integral from `[0,1]` to the Haar integral on `UC`.
  classical
  unfold innerFull innerFullUC
  -- `integral_μ_eq_intervalIntegral` is `∫_UC = ∫_0..1`, so rewrite and symmetrize.
  simpa [MajorArcStep17MajorMinorSplit.innerIntegrand, mul_assoc] using
    (MajorArcStep16CircleToInterval.integral_μ_eq_intervalIntegral
      (f := fun α : UC =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * expSum X N (α - (β : UC)) * expSum X N (α + (β : UC)))).symm

private lemma innerFullUC_eq_sum_nm (X N : ℕ) (β : UC) :
    innerFullUC X N β
      =
    ∑ n ∈ s N, ∑ m ∈ s N,
      aTerm X n * aTerm X m
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
        * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
        * (if n + m = N then 1 else 0) := by
  classical
  unfold innerFullUC

  -- Expand each shifted exponential sum in the standard Step 12 form.
  let fn : ℕ → UC → ℂ := fun n α =>
    aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
      * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
  let gm : ℕ → UC → ℂ := fun m α =>
    aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ)
      * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)

  have hExpSub (α : UC) : expSum X N (α - β) = ∑ n ∈ s N, fn n α := by
    simpa [fn, mul_assoc] using
      (sum_aTerm_fourier_mul_fourier_neg_eq_expSum_sub (X := X) (N := N) (α := α) (β := β)).symm
  have hExpAdd (α : UC) : expSum X N (α + β) = ∑ m ∈ s N, gm m α := by
    simpa [gm, mul_assoc] using
      (sum_aTerm_fourier_mul_fourier_eq_expSum_add (X := X) (N := N) (α := α) (β := β)).symm

  have hfun (α : UC) :
      (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * expSum X N (α - β) * expSum X N (α + β)
        =
      ∑ n ∈ s N, ∑ m ∈ s N,
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) := by
    -- Expand the product of sums pointwise, but keep the algebra linear to avoid `simp` blowups.
    rw [hExpSub, hExpAdd]
    -- abbreviate the `α`-dependent Fourier prefactor
    set f : ℂ := (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
    -- `f * (∑n fn n) = ∑n (f * fn n)`
    have h1 :
        f * (∑ n ∈ s N, fn n α)
          =
        ∑ n ∈ s N, f * fn n α := by
      simp [Finset.mul_sum, mul_assoc]
    -- Multiply by the `m`-sum and expand linearly.
    calc
      f * (∑ n ∈ s N, fn n α) * (∑ m ∈ s N, gm m α)
          =
        (∑ n ∈ s N, f * fn n α) * (∑ m ∈ s N, gm m α) := by
          simpa [mul_assoc] using congrArg (fun z : ℂ => z * (∑ m ∈ s N, gm m α)) h1
      _ =
        ∑ n ∈ s N, (f * fn n α) * (∑ m ∈ s N, gm m α) := by
          simp [Finset.sum_mul]
      _ =
        ∑ n ∈ s N, ∑ m ∈ s N, (f * fn n α) * gm m α := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [Finset.mul_sum, mul_assoc]
      _ =
        ∑ n ∈ s N, ∑ m ∈ s N, f * (fn n α * gm m α) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          refine Finset.sum_congr rfl ?_
          intro m hm
          simp [mul_assoc]
      _ =
        ∑ n ∈ s N, ∑ m ∈ s N, (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) := by
          simp [f]

  have hint_nm :
      ∀ n ∈ s N, ∀ m ∈ s N,
        Integrable (fun α : UC =>
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) μ := by
    intro n hn m hm
    -- Follow the Step 10 pattern: integrable by boundedness on the compact group.
    refine Integrable.of_bound ?_ (‖aTerm X n‖ * ‖aTerm X m‖) ?_
    · -- measurability
      have hcont :
          Continuous fun α : UC =>
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) := by
        fun_prop
      exact hcont.aestronglyMeasurable
    · -- uniform bound
      refine Filter.Eventually.of_forall ?_
      intro α
      -- `‖fourier⋯‖ = 1` pointwise, and `‖fn‖ = ‖aTerm‖`, `‖gm‖ = ‖aTerm‖`.
      calc
        ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)‖
            =
          ‖fourier (T := (1 : ℝ)) (-(N : ℤ)) α‖ * ‖fn n α‖ * ‖gm m α‖ := by
            simp [mul_assoc, mul_left_comm, mul_comm]
        _ ≤ 1 * (‖aTerm X n‖ * 1) * (‖aTerm X m‖ * 1) := by
            have hfn' : ‖fn n α‖ = ‖aTerm X n‖ := by
              simp [fn, mul_assoc, fourier_apply]
            have hgm' : ‖gm m α‖ = ‖aTerm X m‖ := by
              simp [gm, mul_assoc, fourier_apply]
            simp [hfn', hgm', fourier_apply, mul_assoc, mul_left_comm, mul_comm]
        _ = ‖aTerm X n‖ * ‖aTerm X m‖ := by ring
        _ ≤ ‖aTerm X n‖ * ‖aTerm X m‖ := le_rfl

  have hint_outer :
      ∀ n ∈ s N,
        Integrable (fun α : UC =>
          ∑ m ∈ s N, (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) μ := by
    intro n hn
    refine integrable_finset_sum (s N) ?_
    intro m hm
    exact hint_nm n hn m hm

  have hswap :
      (∫ α : UC,
          (∑ n ∈ s N, ∑ m ∈ s N,
              (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) ∂μ)
        =
      ∑ n ∈ s N, ∑ m ∈ s N,
        (∫ α : UC,
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) ∂μ) := by
    -- swap outer sum
    have hsum1 :
        (∫ α : UC,
            (∑ n ∈ s N, ∑ m ∈ s N,
                (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) ∂μ)
          =
        ∑ n ∈ s N,
          (∫ α : UC,
              (∑ m ∈ s N,
                  (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) ∂μ) := by
      simpa using
        (integral_finset_sum (μ := μ) (s := s N)
          (f := fun n (α : UC) =>
            ∑ m ∈ s N, (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α))
          hint_outer)
    rw [hsum1]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hint_m :
        ∀ m ∈ s N,
          Integrable (fun α : UC =>
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) μ := by
      intro m hm
      exact hint_nm n hn m hm
    simpa using
      (integral_finset_sum (μ := μ) (s := s N)
        (f := fun m (α : UC) =>
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α))
        hint_m)

  have hterm (n : ℕ) (hn : n ∈ s N) (m : ℕ) (hm : m ∈ s N) :
      (∫ α : UC,
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) ∂μ)
        =
      aTerm X n * aTerm X m
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
        * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
        * (if n + m = N then 1 else 0) := by
    -- Combine the α-dependent Fourier factors into one character and apply `delta_eq_integral_fourier`.
    set cβ : ℂ :=
      aTerm X n * aTerm X m
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
        * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
    have hαchar (α : UC) :
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ)
          =
        (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) := by
      have hnm :
          (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ)) α : ℂ)
            =
          (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) * fourier (T := (1 : ℝ)) (m : ℤ) α := by
        simpa using (fourier_add (T := (1 : ℝ)) (m := (n : ℤ)) (n := (m : ℤ)) (x := α))
      have hfull :
          (fourier (T := (1 : ℝ)) (((n : ℤ) + (m : ℤ)) + (-(N : ℤ))) α : ℂ)
            =
          (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ)) α : ℂ)
            * fourier (T := (1 : ℝ)) (-(N : ℤ)) α := by
        simpa using
          (fourier_add (T := (1 : ℝ)) (m := (n : ℤ) + (m : ℤ)) (n := (-(N : ℤ))) (x := α))
      calc
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ)
            =
          (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
        _ =
          (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ)) α : ℂ)
            * (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) := by
              simp [hnm, mul_assoc]
        _ = (fourier (T := (1 : ℝ)) (((n : ℤ) + (m : ℤ)) + (-(N : ℤ))) α : ℂ) := by
              simpa [hfull] using hfull.symm
        _ = (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) := by
              simp [add_assoc]
    have hdelta :
        (∫ α : UC, (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) ∂μ)
          =
        (if n + m = N then (1 : ℂ) else 0) := by
      simpa using (delta_eq_integral_fourier (n := n) (m := m) (N := N)).symm
    have hrew :
        (fun α : UC =>
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α))
          =
        fun α : UC => cβ * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) := by
      funext α
      have := hαchar α
      simp [fn, gm, cβ, this, mul_assoc]
      ring_nf
    calc
      (∫ α : UC,
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) ∂μ)
          =
        ∫ α : UC, cβ * (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) ∂μ := by
            refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
            funext α
            simpa using congrArg (fun f : UC → ℂ => f α) hrew
      _ = cβ *
          (∫ α : UC, (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ) ∂μ) := by
            simpa using (integral_const_mul (μ := μ) (r := cβ)
              (f := fun α : UC => (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) α : ℂ)))
      _ = cβ * (if n + m = N then 1 else 0) := by
            exact congrArg (fun z : ℂ => cβ * z) hdelta
      _ = aTerm X n * aTerm X m
            * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
            * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
            * (if n + m = N then 1 else 0) := by
            simp [cβ, mul_assoc, mul_left_comm, mul_comm]

  -- Put it all together.
  calc
    (∫ α : UC,
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * expSum X N (α - β) * expSum X N (α + β) ∂μ)
        =
      ∫ α : UC, (∑ n ∈ s N, ∑ m ∈ s N,
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α)) ∂μ := by
          refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
          funext α
          simpa using hfun α
    _ =
      ∑ n ∈ s N, ∑ m ∈ s N,
        (∫ α : UC,
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ) * (fn n α * gm m α) ∂μ) := by
          exact hswap
    _ =
      ∑ n ∈ s N, ∑ m ∈ s N,
        aTerm X n * aTerm X m
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
          * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
          * (if n + m = N then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          refine Finset.sum_congr rfl ?_
          intro m hm
          simpa using hterm n hn m hm

/-!
## A single-sum Fourier series for `innerFull`

The `α`-orthogonality identity collapses the double sum to a single sum by taking `m = N - n`.
This exposes `innerFull` as a Fourier polynomial in `β` with frequencies `N - 2n`.
-/

private lemma innerFullUC_eq_sum_n (X N : ℕ) (β : UC) :
    innerFullUC X N β
      =
    ∑ n ∈ s N,
      aTerm X n * aTerm X (N - n)
        * (fourier (T := (1 : ℝ)) ((N : ℤ) - 2 * (n : ℤ)) β : ℂ) := by
  classical
  -- Start from the already-expanded double sum and collapse the `m`-sum.
  rw [innerFullUC_eq_sum_nm (X := X) (N := N) (β := β)]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hm : N - n ∈ s N := mem_s_sub_of_mem_s (N := N) (n := n) hn
  have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
  have huniq : ∀ {m : ℕ}, n + m = N → m = N - n := by
    intro m hnm
    have := congrArg (fun t : ℕ => t - n) hnm
    simpa [Nat.add_sub_cancel_left] using this
  -- Evaluate the inner sum by isolating the unique `m = N - n` term.
  have hcollapse :
      (∑ m ∈ s N,
          aTerm X n * aTerm X m
            * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
            * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
            * (if n + m = N then 1 else 0))
        =
      aTerm X n * aTerm X (N - n)
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
        * (fourier (T := (1 : ℝ)) ((N - n : ℕ) : ℤ) β : ℂ) := by
    have hsum :
        (∑ m ∈ s N,
            aTerm X n * aTerm X m
              * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
              * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
              * (if n + m = N then 1 else 0))
          =
        (∑ m ∈ s N,
            if n + m = N then
              aTerm X n * aTerm X m
                * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
                * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
            else 0) := by
      refine Finset.sum_congr rfl ?_
      intro m hm'
      by_cases hnm : n + m = N <;> simp [hnm, mul_assoc, mul_left_comm, mul_comm]
    rw [hsum]
    rw [Finset.sum_eq_single (N - n)]
    · have hnm : n + (N - n) = N := Nat.add_sub_of_le hn_le
      rw [if_pos hnm]
    · intro m hm' hne
      by_cases hnm : n + m = N
      · exact (hne (huniq hnm)).elim
      · simp [hnm]
    · intro hnot
      exact (hnot hm).elim
  -- Convert the product of characters to a single character.
  -- `fourier m * fourier (-n) = fourier (m - n)`, and we rewrite `m = N - n`.
  have hchar :
      (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
        * (fourier (T := (1 : ℝ)) ((N - n : ℕ) : ℤ) β : ℂ)
        =
      (fourier (T := (1 : ℝ)) ((N : ℤ) - 2 * (n : ℤ)) β : ℂ) := by
    -- `((N - n : ℕ) : ℤ) = (N : ℤ) - (n : ℤ)` because `n ≤ N`.
    have hcast : ((N - n : ℕ) : ℤ) = (N : ℤ) - (n : ℤ) := by
      simpa using (Int.ofNat_sub hn_le)
    -- Multiply characters and simplify the exponent.
    have hmul :
        (fourier (T := (1 : ℝ)) ((N : ℤ) - (n : ℤ)) β : ℂ)
            * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
          =
        (fourier (T := (1 : ℝ)) (((N : ℤ) - (n : ℤ)) + (-(n : ℤ))) β : ℂ) := by
      simpa using
        (fourier_add (T := (1 : ℝ)) (m := ((N : ℤ) - (n : ℤ))) (n := (-(n : ℤ))) (x := β)).symm
    calc
      (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
          * (fourier (T := (1 : ℝ)) ((N - n : ℕ) : ℤ) β : ℂ)
          =
        (fourier (T := (1 : ℝ)) ((N - n : ℕ) : ℤ) β : ℂ)
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ) := by
            simp [mul_comm]
      _ =
        (fourier (T := (1 : ℝ)) ((N : ℤ) - (n : ℤ)) β : ℂ)
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ) := by
            simp [hcast]
      _ =
        (fourier (T := (1 : ℝ)) (((N : ℤ) - (n : ℤ)) + (-(n : ℤ))) β : ℂ) := by
            simpa using hmul
      _ =
        (fourier (T := (1 : ℝ)) ((N : ℤ) - 2 * (n : ℤ)) β : ℂ) := by
            ring_nf
  -- Finish by rewriting the collapsed `m`-term and reassociating.
  calc
    (∑ m ∈ s N,
        aTerm X n * aTerm X m
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
          * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)
          * (if n + m = N then 1 else 0))
        =
      aTerm X n * aTerm X (N - n)
        * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
        * (fourier (T := (1 : ℝ)) ((N - n : ℕ) : ℤ) β : ℂ) := hcollapse
    _ =
      aTerm X n * aTerm X (N - n)
        * (fourier (T := (1 : ℝ)) ((N : ℤ) - 2 * (n : ℤ)) β : ℂ) := by
          -- Reassociate so we can apply `hchar`.
          have :=
            congrArg (fun z : ℂ => aTerm X n * aTerm X (N - n) * z) hchar
          simpa [mul_assoc] using this

private lemma innerFullUC_l2_sq_le (X N : ℕ) :
    (∫ β : UC, ‖innerFullUC X N β‖ ^ 2 ∂μ)
      ≤
    ((s N).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
  classical
  -- Fourier polynomial description.
  have hpoly : ∀ β : UC,
      innerFullUC X N β =
        ∑ n ∈ s N,
          (aTerm X n * aTerm X (N - n))
            * (fourier (T := (1 : ℝ)) ((N : ℤ) - 2 * (n : ℤ)) β : ℂ) := by
    intro β
    simpa [mul_assoc] using innerFullUC_eq_sum_n (X := X) (N := N) (β := β)

  -- Coefficients and frequencies.
  let c : ℕ → ℂ := fun n => aTerm X n * aTerm X (N - n)
  let κ : ℕ → ℤ := fun n => (N : ℤ) - 2 * (n : ℤ)

  have hκ_inj : Function.Injective fun n : ℕ => κ n := by
    intro n m hnm
    have h2 :
        (2 : ℤ) * (n : ℤ) = (2 : ℤ) * (m : ℤ) := by
      have := congrArg (fun t : ℤ => (N : ℤ) - t) hnm
      simpa [κ, sub_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using this
    have h2ne : (2 : ℤ) ≠ 0 := by decide
    have : (n : ℤ) = (m : ℤ) := mul_left_cancel₀ h2ne h2
    exact Int.ofNat.inj this

  -- Parseval identity for this Fourier polynomial, via the `L²` orthonormality of `fourierLp`.
  have hparseval :
      (∫ β : UC, ‖innerFullUC X N β‖ ^ 2 ∂μ)
        =
      ∑ n ∈ s N, ‖c n‖ ^ 2 := by
    -- Package the polynomial as a continuous map.
    let f : C(UC, ℂ) :=
      ∑ n ∈ s N, (c n) • (fourier (T := (1 : ℝ)) (κ n))
    have hf : ∀ β : UC, f β = innerFullUC X N β := by
      intro β
      -- `•` is multiplication in `ℂ`.
      simpa [f, hpoly β, c, κ, smul_eq_mul, mul_assoc] using (hpoly β).symm

    -- Orthonormality of the relevant Fourier monomials.
    have hv : Orthonormal ℂ (fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal))) := by
      simpa using (orthonormal_fourier (T := (1 : ℝ)))
    have hv' : Orthonormal ℂ fun n : ℕ => fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (κ n) :=
      hv.comp κ hκ_inj

    -- Compute `⟪toLp f, toLp f⟫` in two ways.
    have hinner_int :
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
          =
        ∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      -- `⟪toLp f, toLp f⟫ = ∫ f * conj f`, and `f * conj f = ‖f‖^2`.
      simpa [RCLike.mul_conj] using (ContinuousMap.inner_toLp (μ := μ) (𝕜 := ℂ) f f)

    have hinner_sum :
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
          =
        ∑ n ∈ s N, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
      -- Push `toLp` through the finite sum and use `Orthonormal.inner_sum`.
      have htoLp :
          ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f
            =
          ∑ n ∈ s N, (c n) • (fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (κ n)) := by
        -- `fourierLp` is defined as `toLp` of the corresponding `fourier` monomial.
        simp [f, fourierLp, map_sum, map_smul]
      -- Now compute the inner product using orthonormality of the `fourierLp` family.
      calc
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
            =
          ⟪∑ n ∈ s N, (c n) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (κ n),
              ∑ n ∈ s N, (c n) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (κ n)⟫_ℂ := by
              simp [htoLp]
        _ = ∑ n ∈ s N, conj (c n) * c n := by
              simpa using (hv'.inner_sum (l₁ := c) (l₂ := c) (s := s N))
        _ = ∑ n ∈ s N, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simpa using (RCLike.conj_mul (c n))

    -- Convert the `ℂ` identity to an `ℝ` identity.
    have hcast_int :
        ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ)
          =
        (∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ) := by
      have h :
          (∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ) := by
        exact
          (integral_ofReal (μ := μ) (f := fun β : UC => ‖f β‖ ^ 2) :
            (∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ))
      exact h.symm
    have hcast_sum :
        ((∑ n ∈ s N, ‖c n‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ s N, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
      simpa using (map_sum Complex.ofRealHom (fun n : ℕ => ‖c n‖ ^ 2) (s N))
    have hEqC' :
        ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ)
          =
        ((∑ n ∈ s N, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
      calc
        ((∫ β : UC, ‖f β‖ ^ 2 ∂μ : ℝ) : ℂ)
            = (∫ β : UC, ((‖f β‖ ^ 2 : ℝ) : ℂ) ∂μ) := hcast_int
        _ = ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
              ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ := by
              symm
              exact hinner_int
        _ = ∑ n ∈ s N, ((‖c n‖ ^ 2 : ℝ) : ℂ) := hinner_sum
        _ = ((∑ n ∈ s N, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
              simpa [hcast_sum] using (hcast_sum.symm)
    have hEqR : (∫ β : UC, ‖f β‖ ^ 2 ∂μ) = ∑ n ∈ s N, ‖c n‖ ^ 2 := by
      -- We already have the equality in `ℂ` between *casts* of the real quantities (`hEqC'`).
      -- Taking real parts immediately gives the desired `ℝ` identity, and avoids coercion pitfalls.
      have h := congrArg (fun z : ℂ => RCLike.re z) hEqC'
      exact (by
        -- Use `simp only` to avoid rewriting the casts via `integral_ofReal`/`map_sum`.
        simpa only [RCLike.ofReal_re] using h)

    -- Rewrite `f` back to `innerFullUC`.
    have hleft :
        (∫ β : UC, ‖innerFullUC X N β‖ ^ 2 ∂μ) = ∫ β : UC, ‖f β‖ ^ 2 ∂μ := by
      refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
      funext β
      simpa [hf β]
    -- And conclude.
    simpa [hleft, hf] using hEqR

  -- Bound the coefficients by `log(N)^2` using `|Λ| ≤ log N`.
  have hcoeff :
      ∀ n ∈ s N, ‖c n‖ ^ 2 ≤ (Real.log (N : ℝ)) ^ 4 := by
    intro n hn
    have hN2 : 2 ≤ N := by
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
      exact le_trans hn2 hn_le
    have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := by
      have h1N : (1 : ℝ) ≤ (N : ℝ) := by
        have : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) hN2
        exact_mod_cast this
      exact Real.log_nonneg h1N
    have hcn :
        ‖aTerm X n‖ ≤ Real.log (N : ℝ) := by
      -- Unfold `aTerm` and use `wX = 1`.
      have hterm : ‖aTerm X n‖ = |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| := by
        simp [aTerm, RCLike.norm_ofReal]
      have hΛ :
          |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| ≤ Real.log (N : ℝ) := by
        simpa [Goldbach.BG_Bank.wX, one_mul] using abs_BG_Lambda_le_log (N := N) (n := n) (hN := hN2) hn
      simpa [hterm] using hΛ
    have hcm :
        ‖aTerm X (N - n)‖ ≤ Real.log (N : ℝ) := by
      have hn' : N - n ∈ s N := mem_s_sub_of_mem_s (N := N) (n := n) hn
      have hterm :
          ‖aTerm X (N - n)‖ = |Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)| := by
        simp [aTerm, RCLike.norm_ofReal]
      have hΛ :
          |Goldbach.BG_Bank.wX X (N - n) * Goldbach.BG_Bank.Λ (N - n)| ≤ Real.log (N : ℝ) := by
        simpa [Goldbach.BG_Bank.wX, one_mul] using
          abs_BG_Lambda_le_log (N := N) (n := (N - n)) (hN := hN2) hn'
      simpa [hterm] using hΛ
    have hmul : ‖c n‖ ≤ Real.log (N : ℝ) * Real.log (N : ℝ) := by
      -- `‖c n‖ = ‖aTerm n‖ * ‖aTerm (N-n)‖`
      have : ‖c n‖ = ‖aTerm X n‖ * ‖aTerm X (N - n)‖ := by
        simp [c, norm_mul]
      -- now bound each factor by `log N`
      calc
        ‖c n‖ = ‖aTerm X n‖ * ‖aTerm X (N - n)‖ := this
        _ ≤ (Real.log (N : ℝ)) * (Real.log (N : ℝ)) := by
              exact mul_le_mul hcn hcm (norm_nonneg _) hlog_nonneg
    -- square both sides
    have hsq' :
        ‖c n‖ ^ 2 ≤ (Real.log (N : ℝ) * Real.log (N : ℝ)) ^ 2 := by
      have h0 : 0 ≤ ‖c n‖ := norm_nonneg _
      have h1 : 0 ≤ Real.log (N : ℝ) * Real.log (N : ℝ) :=
        mul_nonneg hlog_nonneg hlog_nonneg
      have hmul2 :
          ‖c n‖ * ‖c n‖
            ≤
          (Real.log (N : ℝ) * Real.log (N : ℝ)) * (Real.log (N : ℝ) * Real.log (N : ℝ)) :=
        mul_le_mul hmul hmul h0 h1
      simpa [pow_two] using hmul2
    have hpow :
        (Real.log (N : ℝ) * Real.log (N : ℝ)) ^ 2 = (Real.log (N : ℝ)) ^ 4 := by
      -- `(a*a)^2 = a^4`
      set a : ℝ := Real.log (N : ℝ)
      calc
        (a * a) ^ 2 = a ^ 2 * a ^ 2 := by
          simpa using (mul_pow a a 2)
        _ = a ^ (2 + 2) := by
          simpa [pow_add] using (pow_add a 2 2).symm
        _ = a ^ 4 := by
          norm_num
        _ = (Real.log (N : ℝ)) ^ 4 := by
          simp [a]
    -- rewrite `(log * log)^2` as `log^4`
    simpa [hpow] using hsq'

  -- Sum over `n`.
  have hsum_le :
      (∑ n ∈ s N, ‖c n‖ ^ 2) ≤ ((s N).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
    have : ∀ n ∈ s N, ‖c n‖ ^ 2 ≤ (Real.log (N : ℝ)) ^ 4 := hcoeff
    calc
      (∑ n ∈ s N, ‖c n‖ ^ 2)
          ≤
        ∑ n ∈ s N, (Real.log (N : ℝ)) ^ 4 := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact this n hn
      _ = ((s N).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
          simp [mul_assoc]

  -- Conclude using Parseval + coefficient bound.
  simpa [hparseval] using hsum_le

/-!
## Convert the `UC` L² bound back to the interval `Iβ = (-1/2, 1/2]`
-/

theorem innerFull_l2_sq_le (X N : ℕ) :
    (∫ β in Iβ, ‖innerFull X N β‖ ^ 2) ≤ ((s N).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
  classical
  -- Parameterize the Haar integral on `UC = AddCircle 1` by the interval `Iβ`.
  have hIβ : Iβ = Set.Ioc aβ (aβ + 1) := by
    simp [Iβ, bβ_eq_aβ_add_one]
  have hEq :
      (∫ β in Iβ, ‖innerFull X N β‖ ^ 2)
        =
      ∫ β : UC, ‖innerFullUC X N β‖ ^ 2 ∂μ := by
    -- `AddCircle.integral_preimage` for `T = 1`, with `t = aβ = -1/2`.
    have hpre :
        (∫ β in Set.Ioc aβ (aβ + (1 : ℝ)), ‖innerFullUC X N (β : UC)‖ ^ 2)
          =
        ∫ β : UC, ‖innerFullUC X N β‖ ^ 2 ∂volume := by
      -- `volume` on `UC` agrees with the normalized Haar measure `μ` when `T = 1`.
      -- We keep the statement in terms of `volume` and convert to `μ` using `integral_haarAddCircle`.
      simpa using (AddCircle.integral_preimage (T := (1 : ℝ)) (t := aβ)
        (f := fun β : UC => (‖innerFullUC X N β‖ ^ 2 : ℝ)))
    have hhaar :
        (∫ β : UC, ‖innerFullUC X N β‖ ^ 2 ∂volume)
          =
        ∫ β : UC, ‖innerFullUC X N β‖ ^ 2 ∂μ := by
      -- `μ` is the normalized Haar measure on `AddCircle 1`, so the scaling is trivial.
      -- This is exactly the same rewrite used in Step 16.
      simpa [Goldbach.Cert.MajorArcStep7FourierOrthogonality.μ] using
        (AddCircle.integral_haarAddCircle (T := (1 : ℝ))
          (f := fun β : UC => (‖innerFullUC X N β‖ ^ 2 : ℝ))).symm
    -- Rewrite `innerFull` using `innerFullUC` pointwise, then apply `hpre`.
    have hpoint :
        (fun β : ℝ => ‖innerFull X N β‖ ^ 2)
          =
        (fun β : ℝ => ‖innerFullUC X N (β : UC)‖ ^ 2) := by
      funext β
      simp [innerFull_eq_innerFullUC]
    -- Combine the equalities.
    calc
      (∫ β in Iβ, ‖innerFull X N β‖ ^ 2)
          =
        ∫ β in Set.Ioc aβ (aβ + (1 : ℝ)), ‖innerFull X N β‖ ^ 2 := by
          simp [hIβ]
      _ =
        ∫ β in Set.Ioc aβ (aβ + (1 : ℝ)), ‖innerFullUC X N (β : UC)‖ ^ 2 := by
          simpa [hpoint]
      _ =
        ∫ β : UC, ‖innerFullUC X N β‖ ^ 2 ∂volume := by
          simpa using hpre
      _ =
        ∫ β : UC, ‖innerFullUC X N β‖ ^ 2 ∂μ := by
          exact hhaar
  -- Apply the `UC` L² bound.
  simpa [hEq] using innerFullUC_l2_sq_le (X := X) (N := N)

theorem innerMajorQ0Remainder_l2_sq_le (X N : ℕ) (Delta : ℝ) :
    (∫ β in Iβ, ‖innerMajorQ0Remainder X N Delta β‖ ^ 2)
      ≤
    (majorArcConstMode X Delta) ^ 2 * ((s N).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
  classical
  -- `innerMajorQ0Remainder = c * innerFull`, so we pull out the constant and use the `innerFull`
  -- L² bound.
  have hrew :
      (fun β : ℝ => ‖innerMajorQ0Remainder X N Delta β‖ ^ 2)
        =
      fun β : ℝ => (majorArcConstMode X Delta) ^ 2 * (‖innerFull X N β‖ ^ 2) := by
    funext β
    -- Use `‖(c:ℂ) * z‖ = |c| * ‖z‖` and `‖(c:ℂ)‖ = |c|`.
    simp [innerMajorQ0Remainder, mul_assoc, mul_left_comm, mul_comm, pow_two, mul_pow]
  have hbound := innerFull_l2_sq_le (X := X) (N := N)
  -- Integrate the pointwise identity and apply the bound.
  calc
    (∫ β in Iβ, ‖innerMajorQ0Remainder X N Delta β‖ ^ 2)
        =
      ∫ β in Iβ, (majorArcConstMode X Delta) ^ 2 * (‖innerFull X N β‖ ^ 2) := by
        simpa [hrew]
    _ =
      (majorArcConstMode X Delta) ^ 2 * (∫ β in Iβ, ‖innerFull X N β‖ ^ 2) := by
        simp [MeasureTheory.integral_const_mul]
    _ ≤
      (majorArcConstMode X Delta) ^ 2 * (((s N).card : ℝ) * (Real.log (N : ℝ)) ^ 4) := by
        exact mul_le_mul_of_nonneg_left hbound (by nlinarith)
    _ = (majorArcConstMode X Delta) ^ 2 * ((s N).card : ℝ) * (Real.log (N : ℝ)) ^ 4 := by
        ring
