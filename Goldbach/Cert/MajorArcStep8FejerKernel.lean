import Goldbach.BG_Identity
import Goldbach.Cert.MajorArcStep7FourierOrthogonality

/-!
Major arcs (Step 8, sigma-agnostic): Fejér kernel as a finite Fourier polynomial on `AddCircle 1`.

The project’s discrete tent weight `K_full_raw U k` is the standard Fejér Fourier coefficient:
it is supported on `|k| ≤ U` and equals `(1/U) * max(1 - |k|/U, 0)`.

This file packages the basic coefficient-extraction lemma:

`∫ fejerKernel(U) * fourier(-k) = K_full_raw(U,k)`

which is the bridge needed to rewrite `n`-sums with `K_full` weights into circle integrals.
-/

namespace Goldbach.Cert
namespace MajorArcStep8FejerKernel

open scoped BigOperators

open Complex MeasureTheory AddCircle

noncomputable section

open Goldbach.Cert.MajorArcStep7FourierOrthogonality

/-- Integer band `[-U, U]`. -/
def band (U : ℕ) : Finset ℤ :=
  Finset.Icc (-(U : ℤ)) (U : ℤ)

/--
Fejér kernel Fourier polynomial with coefficients `K_full_raw U k`, viewed as a function on
`AddCircle 1`.
-/
noncomputable def fejerKernel (U : ℕ) (x : UC) : ℂ :=
  ∑ k ∈ band U, (Goldbach.BG_Identity.K_full_raw U k : ℂ) * fourier (T := (1 : ℝ)) k x

private lemma integrable_fejerKernel_term (U : ℕ) (k0 k : ℤ) :
    Integrable
        (fun x : UC =>
          (Goldbach.BG_Identity.K_full_raw U k : ℂ) * fourier (T := (1 : ℝ)) k x *
            fourier (T := (1 : ℝ)) (-k0) x)
        μ := by
  -- `AddCircle.haarAddCircle` is finite (in fact, it has mass `1`), and the integrand is bounded.
  refine Integrable.of_bound ?_ (‖(Goldbach.BG_Identity.K_full_raw U k : ℂ)‖) ?_
  · -- measurability: continuous function on a measurable space
    have hcont :
        Continuous fun x : UC =>
          (Goldbach.BG_Identity.K_full_raw U k : ℂ) * fourier (T := (1 : ℝ)) k x *
            fourier (T := (1 : ℝ)) (-k0) x := by
      simpa [mul_assoc] using
        (continuous_const.mul ((fourier (T := (1 : ℝ)) k).continuous.mul
          (fourier (T := (1 : ℝ)) (-k0)).continuous))
    exact hcont.aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro x
    -- `fourier` values lie on the unit circle, so the product has norm `‖coeff‖`.
    have hk : ‖fourier (T := (1 : ℝ)) k x‖ = 1 := by
      simpa using Circle.norm_coe (toCircle ((k : ℤ) • x))
    have hk0 : ‖fourier (T := (1 : ℝ)) (-k0) x‖ = 1 := by
      simpa using Circle.norm_coe (toCircle ((-k0 : ℤ) • x))
    calc
      ‖(Goldbach.BG_Identity.K_full_raw U k : ℂ) * fourier (T := (1 : ℝ)) k x *
            fourier (T := (1 : ℝ)) (-k0) x‖
          = ‖(Goldbach.BG_Identity.K_full_raw U k : ℂ)‖ *
              ‖fourier (T := (1 : ℝ)) k x‖ * ‖fourier (T := (1 : ℝ)) (-k0) x‖ := by
              simp [mul_assoc, norm_mul]
      _ = ‖(Goldbach.BG_Identity.K_full_raw U k : ℂ)‖ := by
              simp [hk, hk0]
      _ ≤ ‖(Goldbach.BG_Identity.K_full_raw U k : ℂ)‖ := le_rfl

/--
Coefficient extraction: integrating the Fejér kernel against `fourier(-k)` picks out the `k`th
coefficient (or `0` if `k` is outside the band).
-/
theorem integral_fejerKernel_mul_fourier_neg (U : ℕ) (k : ℤ) :
    (∫ x : UC, fejerKernel U x * (fourier (T := (1 : ℝ)) (-k) x : ℂ) ∂μ)
      =
    if k ∈ band U then (Goldbach.BG_Identity.K_full_raw U k : ℂ) else 0 := by
  classical
  -- Expand the finite sum and swap integral/sum.
  have hint : (∀ i ∈ band U, Integrable
      (fun x : UC =>
        (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
          fourier (T := (1 : ℝ)) (-k) x) μ) := by
    intro i hi
    simpa [mul_assoc] using integrable_fejerKernel_term (U := U) (k0 := k) (k := i)

  simp [fejerKernel, band, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm,
    integral_finset_sum (μ := μ) (s := band U)
      (f := fun i x =>
        (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
          fourier (T := (1 : ℝ)) (-k) x)
      hint,
    integral_mul_left, integral_mul_right]  -- reduces to integrals of `fourier (i-k)`

  -- After `simp`, the remaining goal is the coefficient collapse via Fourier orthogonality.

*** End Patch}Oops, the apply_patch tool expects FREEFORM input, not JSON. Let's redo properly. We'll craft patch in correct format. I mistakenly invoked tool with JSON. We'll retry. Let's call apply_patch with freeform. We'll need to include final proof; my patch is incomplete after simp. Better to write full file carefully now, not leave unfinished. We'll re-do apply_patch adding file complete with proof. Let's plan proof more precisely before patching again.
