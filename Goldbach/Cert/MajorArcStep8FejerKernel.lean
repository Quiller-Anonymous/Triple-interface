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
  refine Integrable.of_bound ?_ (‖(Goldbach.BG_Identity.K_full_raw U k : ℂ)‖) ?_
  · have hcont :
        Continuous fun x : UC =>
          (Goldbach.BG_Identity.K_full_raw U k : ℂ) * fourier (T := (1 : ℝ)) k x *
            fourier (T := (1 : ℝ)) (-k0) x := by
      simpa [mul_assoc] using
        (continuous_const.mul ((fourier (T := (1 : ℝ)) k).continuous.mul
          (fourier (T := (1 : ℝ)) (-k0)).continuous))
    exact hcont.aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro x
    calc
      ‖(Goldbach.BG_Identity.K_full_raw U k : ℂ) * fourier (T := (1 : ℝ)) k x *
            fourier (T := (1 : ℝ)) (-k0) x‖
          = ‖(Goldbach.BG_Identity.K_full_raw U k : ℂ)‖ *
              ‖fourier (T := (1 : ℝ)) k x‖ * ‖fourier (T := (1 : ℝ)) (-k0) x‖ := by
              simp [mul_assoc]
      _ = ‖(Goldbach.BG_Identity.K_full_raw U k : ℂ)‖ := by
              simp [fourier_apply]
      _ ≤ ‖(Goldbach.BG_Identity.K_full_raw U k : ℂ)‖ := le_rfl

private lemma integral_fourier_eq_ite (n : ℤ) :
    (∫ x : UC, (fourier (T := (1 : ℝ)) n x : ℂ) ∂μ) = if n = 0 then 1 else 0 := by
  simpa [μ] using (Goldbach.Cert.MajorArcStep7FourierOrthogonality.integral_fourier (n := n))

/--
Coefficient extraction: integrating the Fejér kernel against `fourier(-k)` picks out the `k`th
coefficient (or `0` if `k` is outside the band).
-/
theorem integral_fejerKernel_mul_fourier_neg (U : ℕ) (k : ℤ) :
    (∫ x : UC, fejerKernel U x * (fourier (T := (1 : ℝ)) (-k) x : ℂ) ∂μ)
      =
    if k ∈ band U then (Goldbach.BG_Identity.K_full_raw U k : ℂ) else 0 := by
  classical
  -- Move multiplication by `fourier(-k)` inside the finite sum.
  have hintegrand :
      (fun x : UC => fejerKernel U x * (fourier (T := (1 : ℝ)) (-k) x : ℂ))
        =
      fun x : UC =>
        ∑ i ∈ band U,
          (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
            fourier (T := (1 : ℝ)) (-k) x := by
    funext x
    dsimp [fejerKernel]
    -- `(∑ i, f i) * a = ∑ i, f i * a`
    simpa [mul_assoc] using
      (Finset.sum_mul (s := band U)
        (f := fun i => (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x)
        (a := (fourier (T := (1 : ℝ)) (-k) x : ℂ)))

  have hint :
      ∀ i ∈ band U,
        Integrable
          (fun x : UC =>
            (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
              fourier (T := (1 : ℝ)) (-k) x)
          μ := by
    intro i hi
    simpa [mul_assoc] using integrable_fejerKernel_term (U := U) (k0 := k) (k := i)

  -- Swap integral and sum.
  have hsum :
      (∫ x : UC,
          (∑ i ∈ band U,
              (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                fourier (T := (1 : ℝ)) (-k) x) ∂μ)
        =
      ∑ i ∈ band U,
        (∫ x : UC,
            (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
              fourier (T := (1 : ℝ)) (-k) x ∂μ) := by
    simpa using
      (integral_finset_sum (μ := μ) (s := band U)
        (f := fun i (x : UC) =>
          (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
            fourier (T := (1 : ℝ)) (-k) x)
        hint)

  -- Evaluate each inner integral by orthogonality.
  have hrewrite :
      (∫ x : UC, fejerKernel U x * (fourier (T := (1 : ℝ)) (-k) x : ℂ) ∂μ)
        =
      (∫ x : UC,
          (∑ i ∈ band U,
              (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                fourier (T := (1 : ℝ)) (-k) x) ∂μ) := by
    refine integral_congr_ae ?_
    exact Filter.EventuallyEq.of_eq hintegrand

  calc
    (∫ x : UC, fejerKernel U x * (fourier (T := (1 : ℝ)) (-k) x : ℂ) ∂μ)
        =
      (∫ x : UC,
          (∑ i ∈ band U,
              (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                fourier (T := (1 : ℝ)) (-k) x) ∂μ) := by
          exact hrewrite
    _ = ∑ i ∈ band U,
          (∫ x : UC,
              (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                fourier (T := (1 : ℝ)) (-k) x ∂μ) := by
          simpa using hsum
    _ =
      ∑ i ∈ band U,
        (Goldbach.BG_Identity.K_full_raw U i : ℂ) *
          (if i = k then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          -- Replace the product of Fourier characters by a single character.
          have hfourier :
              ∀ x : UC,
                (fourier (T := (1 : ℝ)) i x : ℂ) * fourier (T := (1 : ℝ)) (-k) x =
                  fourier (T := (1 : ℝ)) (i + -k) x := by
            intro x
            exact (fourier_add (T := (1 : ℝ)) (m := i) (n := -k) (x := x)).symm
          have hmul :
              (∫ x : UC,
                  (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                    fourier (T := (1 : ℝ)) (-k) x ∂μ)
                =
              (Goldbach.BG_Identity.K_full_raw U i : ℂ)
                * (∫ x : UC, (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) ∂μ) := by
            -- rewrite the integrand pointwise using `hfourier`, then pull out the constant.
            have hfun :
                (fun x : UC =>
                  (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                    fourier (T := (1 : ℝ)) (-k) x)
                  =
                fun x : UC =>
                  (Goldbach.BG_Identity.K_full_raw U i : ℂ) *
                    (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) := by
              funext x
              calc
                (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                      fourier (T := (1 : ℝ)) (-k) x
                    =
                    (Goldbach.BG_Identity.K_full_raw U i : ℂ) *
                      ((fourier (T := (1 : ℝ)) i x : ℂ) * fourier (T := (1 : ℝ)) (-k) x) := by
                      exact (mul_assoc _ _ _)
                _ =
                    (Goldbach.BG_Identity.K_full_raw U i : ℂ) *
                      (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) := by
                      exact congrArg (fun z : ℂ => (Goldbach.BG_Identity.K_full_raw U i : ℂ) * z)
                        (hfourier x)
            have hfun_ae :
                (fun x : UC =>
                    (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                      fourier (T := (1 : ℝ)) (-k) x)
                  =ᵐ[μ]
                fun x : UC =>
                    (Goldbach.BG_Identity.K_full_raw U i : ℂ) *
                      (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) :=
              Filter.EventuallyEq.of_eq hfun
            have hrewrite :
                (∫ x : UC,
                    (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                      fourier (T := (1 : ℝ)) (-k) x ∂μ)
                  =
                (∫ x : UC,
                    (Goldbach.BG_Identity.K_full_raw U i : ℂ) *
                      (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) ∂μ) :=
              integral_congr_ae hfun_ae
            calc
              (∫ x : UC,
                  (Goldbach.BG_Identity.K_full_raw U i : ℂ) * fourier (T := (1 : ℝ)) i x *
                    fourier (T := (1 : ℝ)) (-k) x ∂μ)
                  =
                (∫ x : UC,
                    (Goldbach.BG_Identity.K_full_raw U i : ℂ) *
                      (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) ∂μ) := hrewrite
              _ =
                (Goldbach.BG_Identity.K_full_raw U i : ℂ)
                  * (∫ x : UC, (fourier (T := (1 : ℝ)) (i + -k) x : ℂ) ∂μ) := by
                    exact
                      (integral_const_mul (μ := μ) (r := (Goldbach.BG_Identity.K_full_raw U i : ℂ))
                        (f := fun x : UC => (fourier (T := (1 : ℝ)) (i + -k) x : ℂ)))
          -- simplify `i + -k = 0` iff `i = k`
          have hiz : (i + -k = 0) ↔ i = k := by
            constructor
            · intro h
              have := congrArg (fun z : ℤ => z + k) h
              simpa [add_assoc] using this
            · intro h
              subst h
              simp
          -- finish the term evaluation
          rw [hmul]
          rw [integral_fourier_eq_ite (n := i + -k)]
          by_cases hik : i = k
          · subst hik
            simp
          · have : i + -k ≠ 0 := by
              intro h0
              exact hik ((hiz.mp h0))
            simp [hik, this]
    _ = if k ∈ band U then (Goldbach.BG_Identity.K_full_raw U k : ℂ) else 0 := by
          -- collapse the sum using the `* ite(k=i) 1 0` selector
          -- (rewrite `if i = k` as `ite (k = i)` to match `sum_mul_boole`).
          simp [band, eq_comm]

end

end MajorArcStep8FejerKernel
end Goldbach.Cert
