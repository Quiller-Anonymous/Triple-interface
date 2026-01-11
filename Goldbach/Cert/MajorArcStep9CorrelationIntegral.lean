import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.Cert.MajorArcStep7FourierOrthogonality

/-!
Major arcs (Step 9, sigma-agnostic): rewrite the smoothed correlation as a Haar integral.

The major-arc exponential sum approximations (Steps 2–6) are statements about Fourier-type sums
`∑ Λ(n) e(α n)`. To apply them to the project’s `RΛ_smooth`, we re-introduce Fourier analysis on
`AddCircle 1`:

* the additive constraint `n + m = N` is represented by orthogonality (Step 7),
* the short-shift restriction `|n-m| ≤ H` with tent weights is represented by a finite Fourier
  polynomial supported on `S_BG`.

This file sets up those identities. It is purely algebraic/measure-theoretic and does not use
Siegel–Walfisz or any σ-specific statements.
-/

namespace Goldbach.Cert
namespace MajorArcStep9CorrelationIntegral

open scoped BigOperators

open Complex MeasureTheory AddCircle

noncomputable section

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcStep7FourierOrthogonality

private abbrev SBG : Finset ℤ := Goldbach.BG_Identity.S_BG

private abbrev Kfull (k : ℤ) : ℝ := Goldbach.BG_Identity.K_full k

/-- The kernel coefficient used by `RΛ_smooth`: `K_full(k)` on `S_BG`, `0` otherwise. -/
noncomputable def coeff (k : ℤ) : ℝ :=
  if k ∈ SBG then Kfull k else 0

/-- Unfold `coeff` in terms of the underlying `BG_Identity` data. -/
theorem coeff_eq (k : ℤ) :
    coeff k =
      if k ∈ Goldbach.BG_Identity.S_BG then Goldbach.BG_Identity.K_full k else 0 := by
  classical
  simp [coeff, SBG, Kfull]

/-- A finite Fourier polynomial whose `k`th coefficient is `coeff k`. -/
noncomputable def kernelPoly (x : UC) : ℂ :=
  ∑ k ∈ SBG, (Kfull k : ℂ) * fourier (T := (1 : ℝ)) k x

/-- Unfold `kernelPoly` in terms of the underlying `BG_Identity` data. -/
theorem kernelPoly_eq (x : UC) :
    kernelPoly x =
      ∑ k ∈ Goldbach.BG_Identity.S_BG,
        (Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k x := by
  classical
  simp [kernelPoly, SBG, Kfull]

theorem integral_kernelPoly_mul_fourier_neg (k : ℤ) :
    (∫ x : UC, kernelPoly x * (fourier (T := (1 : ℝ)) (-k) x : ℂ) ∂μ) = (coeff k : ℂ) := by
  classical
  -- Expand the finite sum and use orthogonality.
  have hint :
      ∀ i ∈ SBG,
        Integrable
          (fun x : UC =>
            (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x)
          μ := by
    intro i hi
    -- `μ` is finite; bound the integrand by `‖Kfull i‖`.
    refine Integrable.of_bound ?_ (‖(Kfull i : ℂ)‖) ?_
    · have hcont :
          Continuous fun x : UC =>
            (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x := by
        simpa [mul_assoc] using
          (continuous_const.mul ((fourier (T := (1 : ℝ)) i).continuous.mul
            (fourier (T := (1 : ℝ)) (-k)).continuous))
      exact hcont.aestronglyMeasurable
    · refine Filter.Eventually.of_forall ?_
      intro x
      -- `‖fourier⋯‖ = 1` pointwise.
      calc
        ‖(Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x‖
            =
          ‖(Kfull i : ℂ)‖ * ‖fourier (T := (1 : ℝ)) i x‖ * ‖fourier (T := (1 : ℝ)) (-k) x‖ := by
              simp [mul_assoc]
        _ = ‖(Kfull i : ℂ)‖ := by
              simp [fourier_apply]
        _ ≤ ‖(Kfull i : ℂ)‖ := le_rfl

  have hsum :
      (∫ x : UC,
          (∑ i ∈ SBG, (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x *
              fourier (T := (1 : ℝ)) (-k) x) ∂μ)
        =
      ∑ i ∈ SBG,
        (∫ x : UC,
            (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x ∂μ) := by
    simpa using
      (integral_finset_sum (μ := μ) (s := SBG)
        (f := fun i (x : UC) =>
          (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x)
        hint)

  -- Evaluate each inner integral.
  have hterm (i : ℤ) :
      (∫ x : UC,
          (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x ∂μ)
        =
      (Kfull i : ℂ) * (if i = k then 1 else 0) := by
    -- rewrite the character product to a single Fourier character
    have hmul :
        (∫ x : UC,
            (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x ∂μ)
          =
        (Kfull i : ℂ) * (∫ x : UC, (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) ∂μ) := by
      -- pointwise rewrite and pull out the constant
      have hfun :
          (fun x : UC =>
              (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x)
            =
          fun x : UC =>
            (Kfull i : ℂ) * (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) := by
        funext x
        have : (fourier (T := (1 : ℝ)) (i + -k) x : ℂ)
              = (fourier (T := (1 : ℝ)) i x : ℂ) * fourier (T := (1 : ℝ)) (-k) x := by
          simpa using (fourier_add (T := (1 : ℝ)) (m := i) (n := -k) (x := x))
        calc
          (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x
              =
            (Kfull i : ℂ) * ((fourier (T := (1 : ℝ)) i x : ℂ) * fourier (T := (1 : ℝ)) (-k) x) := by
              exact (mul_assoc _ _ _)
          _ = (Kfull i : ℂ) * (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) := by
              exact congrArg (fun z : ℂ => (Kfull i : ℂ) * z) this.symm
      have hfun_ae : (fun x : UC =>
          (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x)
          =ᵐ[μ]
          fun x : UC => (Kfull i : ℂ) * (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) :=
        Filter.EventuallyEq.of_eq hfun
      have hrewrite := integral_congr_ae hfun_ae
      calc
        (∫ x : UC,
            (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x * fourier (T := (1 : ℝ)) (-k) x ∂μ)
            =
          (∫ x : UC,
              (Kfull i : ℂ) * (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) ∂μ) := hrewrite
        _ = (Kfull i : ℂ) * (∫ x : UC, (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) ∂μ) := by
              simpa using
                (integral_const_mul (μ := μ) (r := (Kfull i : ℂ))
                  (f := fun x : UC => (fourier (T := (1 : ℝ)) (i + -k) x : ℂ)))

    -- use Step 7 to evaluate the integral
    have hiz : (i + -k = 0) ↔ i = k := by
      constructor
      · intro h
        have := congrArg (fun z : ℤ => z + k) h
        simpa [add_assoc] using this
      · intro h
        subst h
        simp
    rw [hmul]
    -- integral of `fourier n` is `if n=0 then 1 else 0`
    rw [Goldbach.Cert.MajorArcStep7FourierOrthogonality.integral_fourier (n := i + -k)]
    by_cases hik : i = k
    · subst hik
      simp
    · have : i + -k ≠ 0 := by
        intro h0
        exact hik (hiz.mp h0)
      simp [hik, this]

  -- Now collapse the sum using `Finset.sum_mul_boole`.
  calc
    (∫ x : UC, kernelPoly x * (fourier (T := (1 : ℝ)) (-k) x : ℂ) ∂μ)
        =
      (∫ x : UC,
          (∑ i ∈ SBG, (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x *
              fourier (T := (1 : ℝ)) (-k) x) ∂μ) := by
        -- unfold `kernelPoly` and distribute `* fourier(-k)`
        have :
            (fun x : UC => kernelPoly x * (fourier (T := (1 : ℝ)) (-k) x : ℂ))
              =
            fun x : UC =>
              ∑ i ∈ SBG, (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x *
                fourier (T := (1 : ℝ)) (-k) x := by
          funext x
          dsimp [kernelPoly]
          simpa [mul_assoc] using
            (Finset.sum_mul (s := SBG)
              (f := fun i => (Kfull i : ℂ) * fourier (T := (1 : ℝ)) i x)
              (a := (fourier (T := (1 : ℝ)) (-k) x : ℂ)))
        refine integral_congr_ae ?_
        exact Filter.EventuallyEq.of_eq this
    _ = ∑ i ∈ SBG,
          (Kfull i : ℂ) * (if i = k then 1 else 0) := by
        -- swap integral and sum, then evaluate each term
        rw [hsum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (hterm i)
    _ = (if k ∈ SBG then (Kfull k : ℂ) else 0) := by
        -- selector sum
        simpa [Finset.sum_mul_boole, eq_comm] using
          (Finset.sum_mul_boole (s := SBG) (f := fun i : ℤ => (Kfull i : ℂ)) (i := k))
    _ = (coeff k : ℂ) := by
        by_cases hk : k ∈ SBG <;> simp [coeff, hk, SBG, Kfull]

/--
Orthogonality for the additive constraint `n + m = N`, expressed as a Haar integral on `AddCircle 1`.
-/
lemma delta_eq_integral_fourier {n m N : ℕ} :
    (if n + m = N then (1 : ℂ) else 0)
      =
    (∫ x : UC, (fourier (T := (1 : ℝ)) ((n : ℤ) + (m : ℤ) + (-(N : ℤ))) x : ℂ) ∂μ) := by
  by_cases h : n + m = N
  · -- the index is `0`, so the integral is `1`
    have hnm : (n : ℤ) + (m : ℤ) = (N : ℤ) := by
      exact_mod_cast h
    have hidx : (n : ℤ) + (m : ℤ) + (-(N : ℤ)) = 0 := by
      simpa [add_assoc] using congrArg (fun z : ℤ => z + (-(N : ℤ))) hnm
    rw [Goldbach.Cert.MajorArcStep7FourierOrthogonality.integral_fourier
      (n := (n : ℤ) + (m : ℤ) + (-(N : ℤ)))]
    simp [h, hidx]
  · have hidx : (n : ℤ) + (m : ℤ) + (-(N : ℤ)) ≠ 0 := by
      intro hz
      have hnm : (n : ℤ) + (m : ℤ) = (N : ℤ) := by
        have := congrArg (fun z : ℤ => z + (N : ℤ)) hz
        simpa [add_assoc] using this
      have : n + m = N := by
        exact_mod_cast hnm
      exact h this
    rw [Goldbach.Cert.MajorArcStep7FourierOrthogonality.integral_fourier
      (n := (n : ℤ) + (m : ℤ) + (-(N : ℤ)))]
    simp [h, hidx]

end

end MajorArcStep9CorrelationIntegral
end Goldbach.Cert
