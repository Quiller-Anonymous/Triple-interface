import Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled

/-!
Major arcs (Step 12, sigma-agnostic): rewrite the Step 10/11 integral in “shifted frequency” form.

The Step 10 integral features the products

* `fourier n α * fourier (-n) β`, and
* `fourier n α * fourier n β`,

coming from the two Fourier manipulations (additive constraint on `α`, kernel coefficient extraction
on `β`).

Since `fourier n` is a character of the additive circle, these products can be rewritten as single
characters at shifted arguments:

* `fourier n (α - β)`, and
* `fourier n (α + β)`.

This file packages those rewrites and introduces a compact exponential-sum notation
`expSum X N γ = ∑_{n∈[2,N-2]} aTerm X n * fourier n γ`.
-/

namespace Goldbach.Cert
namespace MajorArcStep12ShiftedExpSums

open scoped BigOperators

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled

noncomputable section

lemma fourier_add_arg (n : ℤ) (x y : UC) :
    (fourier (T := (1 : ℝ)) n (x + y) : ℂ)
      =
    (fourier (T := (1 : ℝ)) n x : ℂ) * (fourier (T := (1 : ℝ)) n y : ℂ) := by
  -- `fourier n` is a character: `fourier n (x+y) = fourier n x * fourier n y`.
  simp [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul, mul_assoc]

lemma fourier_neg_arg (n : ℤ) (x : UC) :
    (fourier (T := (1 : ℝ)) n (-x) : ℂ) = (fourier (T := (1 : ℝ)) (-n) x : ℂ) := by
  -- Both sides are `toCircle (-(n • x))`.
  simp [fourier_apply, zsmul_neg, neg_zsmul]

lemma fourier_mul_fourier_neg_eq_sub (n : ℤ) (α β : UC) :
    (fourier (T := (1 : ℝ)) n α : ℂ) * (fourier (T := (1 : ℝ)) (-n) β : ℂ)
      =
    (fourier (T := (1 : ℝ)) n (α - β) : ℂ) := by
  -- Rewrite `fourier (-n) β` as `fourier n (-β)` and use additivity in the argument.
  have hneg : (fourier (T := (1 : ℝ)) (-n) β : ℂ) = (fourier (T := (1 : ℝ)) n (-β) : ℂ) := by
    simpa using (fourier_neg_arg (n := n) (x := β)).symm
  have hadd := fourier_add_arg (n := n) (x := α) (y := -β)
  -- `hadd.symm : fourier n α * fourier n (-β) = fourier n (α + -β)`.
  calc
    (fourier (T := (1 : ℝ)) n α : ℂ) * (fourier (T := (1 : ℝ)) (-n) β : ℂ)
        =
      (fourier (T := (1 : ℝ)) n α : ℂ) * (fourier (T := (1 : ℝ)) n (-β) : ℂ) := by
        simpa [hneg]
    _ =
      (fourier (T := (1 : ℝ)) n (α + (-β)) : ℂ) := by
        simpa using hadd.symm
    _ = (fourier (T := (1 : ℝ)) n (α - β) : ℂ) := by
        simp [sub_eq_add_neg]

lemma fourier_mul_fourier_eq_add (n : ℤ) (α β : UC) :
    (fourier (T := (1 : ℝ)) n α : ℂ) * (fourier (T := (1 : ℝ)) n β : ℂ)
      =
    (fourier (T := (1 : ℝ)) n (α + β) : ℂ) := by
  simpa using (fourier_add_arg (n := n) (x := α) (y := β)).symm

/-- Exponential sum on the circle: `∑_{n∈[2,N-2]} aTerm X n * fourier(n) γ`. -/
noncomputable def expSum (X N : ℕ) (γ : UC) : ℂ :=
  ∑ n ∈ s N, aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)

lemma sum_aTerm_fourier_mul_fourier_neg_eq_expSum_sub (X N : ℕ) (α β : UC) :
    (∑ n ∈ s N,
        aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
      =
    expSum X N (α - β) := by
  classical
  unfold expSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  -- Use the character identity on `α - β`.
  have hchar :=
    fourier_mul_fourier_neg_eq_sub (n := (n : ℤ)) (α := α) (β := β)
  -- Reassociate to match the `aTerm * (fourier * fourier)` shape.
  -- Avoid aggressive `simp`; keep the rewrite local.
  calc
    aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)
        =
      aTerm X n * ((fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
          * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ)) := by
        ring
    _ = aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) (α - β) : ℂ) := by
        simpa [mul_assoc] using congrArg (fun z : ℂ => aTerm X n * z) hchar

lemma sum_aTerm_fourier_mul_fourier_eq_expSum_add (X N : ℕ) (α β : UC) :
    (∑ n ∈ s N,
        aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
          * (fourier (T := (1 : ℝ)) (n : ℤ) β : ℂ))
      =
    expSum X N (α + β) := by
  classical
  unfold expSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hchar := fourier_mul_fourier_eq_add (n := (n : ℤ)) (α := α) (β := β)
  calc
    aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
          * (fourier (T := (1 : ℝ)) (n : ℤ) β : ℂ)
        =
      aTerm X n * ((fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
          * (fourier (T := (1 : ℝ)) (n : ℤ) β : ℂ)) := by
        ring
    _ = aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) (α + β) : ℂ) := by
        simpa [mul_assoc] using congrArg (fun z : ℂ => aTerm X n * z) hchar

/-- Step 11’s `corr_integral` rewritten using the shifted exponential sums `expSum X N (α±β)`. -/
theorem corr_integral_eq_shifted (X N : ℕ) :
    corr_integral X N
      =
    ∫ β : UC, kernelPolyC β *
      (∫ α : UC,
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            * (expSum X N (α - β))
            * (expSum X N (α + β))
        ∂μ)
    ∂μ := by
  classical
  -- Unfold the definition and rewrite both inner `n`-sums.
  unfold corr_integral
  refine integral_congr_ae (Filter.EventuallyEq.of_eq ?_)
  funext β
  -- Rewrite the inner `α`-integral by pointwise rewriting of the integrand.
  have hsub (α : UC) :
      (∑ n ∈ s N,
          aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
        =
      expSum X N (α - β) :=
    sum_aTerm_fourier_mul_fourier_neg_eq_expSum_sub (X := X) (N := N) (α := α) (β := β)
  have hadd (α : UC) :
      (∑ m ∈ s N,
          aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ)
            * (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ))
        =
      expSum X N (α + β) :=
    sum_aTerm_fourier_mul_fourier_eq_expSum_add (X := X) (N := N) (α := α) (β := β)

  have hα :
      (fun α : UC =>
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            *
            (∑ n ∈ s N,
              aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) *
                (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
            *
            (∑ m ∈ s N,
              aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ) *
                (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ)))
        =
      fun α : UC =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
          * (expSum X N (α - β))
          * (expSum X N (α + β)) := by
    funext α
    -- Rewrite the two sums first, before any simp lemmas expand `fourier`.
    rw [hsub α, hadd α]

  have hinter :
      (∫ α : UC,
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            *
            (∑ n ∈ s N,
              aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) α : ℂ) *
                (fourier (T := (1 : ℝ)) (-(n : ℤ)) β : ℂ))
            *
            (∑ m ∈ s N,
              aTerm X m * (fourier (T := (1 : ℝ)) (m : ℤ) α : ℂ) *
                (fourier (T := (1 : ℝ)) (m : ℤ) β : ℂ))
        ∂μ)
        =
      (∫ α : UC,
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            * (expSum X N (α - β))
            * (expSum X N (α + β))
        ∂μ) := by
    simpa using integral_congr_ae (Filter.EventuallyEq.of_eq hα)

  -- Finish by rewriting the inner integral; avoid `simp`-cancellation on the `kernelPolyC β` factor.
  simpa [mul_assoc] using congrArg (fun z : ℂ => kernelPolyC β * z) hinter

end

end MajorArcStep12ShiftedExpSums
end Goldbach.Cert
