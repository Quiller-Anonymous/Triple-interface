import SSU.Engines.BGTypeIIData
import SSU.Torus.Basic
import Mathlib.Analysis.Fourier.AddCircle

/-!
05_BG.tex — Type–II coefficient array and product aggregation (`A_k`) (TeX-faithful).

This file defines the **map** from a TeX-style factorized Type–II array

`F(d,n) = α_d β_n W(d/D,n/N)`

on a BG tube `T(a/q,s)` to its aggregated product coefficients

`A_k := ∑_{dn=k} F(d,n)` (TeX Eq. (5.2)),

and the associated torus exponential sum in the product variable

`S(x) := ∑_k A_k * fourier k x`.

It is purely algebraic/bookkeeping: no analytic bounds and no packet/SSU heart content.
-/

namespace SSU
namespace Engines
namespace BGTypeIIArray

open scoped BigOperators

noncomputable section

open SSU.Torus
open SSU.Engines.TypeII.ProductToeplitz

abbrev TubePoint : Type := SSU.TubePoint

/-!
## TeX factorization → coefficient array
-/

structure Data (H : Type*) where
  /-- BG tube parameters `(X,H,D,N,U; a,q,s)` (TeX: def-tube). -/
  TP : SSU.Engines.BGTypeII.TubeParams
  /-- TFA cutoff `W(d/D,n/N)` (03_TFA.tex). -/
  W : SSU.Engines.TFA.Weight
  /-- Coefficients `α_d` (depends on the application; may depend on `f,i,j`). -/
  α : H → ℤ → ℤ → ℤ → ℂ
  /-- Coefficients `β_n` (depends on the application; may depend on `f,i,j`). -/
  β : H → ℤ → ℤ → ℤ → ℂ

namespace Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (D : Data H)

noncomputable def C : SSU.Engines.BGToeplitzReduction.TeX.CoeffFactorization (H := H) :=
  SSU.Engines.BGTypeII.TeX.mkCoeffFactorization (H := H) D.TP D.W D.α D.β

noncomputable def tube : Finset TubePoint :=
  (D.C).tube

/-!
### Box specialization (05_BG “Toeplitz block”)

The TeX Toeplitz regrouping identity (Eq. (5.2)/(5.3) ⇒ the displayed `k,k'` sum) is naturally
stated on the full dyadic box `(D,2D]×(N,2N]` (with a smooth cutoff), before any specialization to
a shear tube.

To reuse the existing tube-based infrastructure, we represent the box as a “tube” via the trivial
choice `a = 0, q = 1, s = 0` and a sufficiently large `U`, so that `tubeFinset = box`.
-/

/-- Construct a `Data` object on the *full dyadic box*, represented as a trivial tube. -/
noncomputable def mkBox
    (P : SSU.Engines.BGTube.Params)
    (hU : 2 * P.N ≤ P.U)
    (W : SSU.Engines.TFA.Weight)
    (α : H → ℤ → ℤ → ℤ → ℂ) (β : H → ℤ → ℤ → ℤ → ℂ) :
    Data H :=
  { TP := SSU.Engines.BGTypeII.TubeParams.boxTube P
    W := W
    α := α
    β := β }

theorem mkBox_tube_eq_box
    (P : SSU.Engines.BGTube.Params)
    (hU : 2 * P.N ≤ P.U)
    (W : SSU.Engines.TFA.Weight)
    (α : H → ℤ → ℤ → ℤ → ℂ) (β : H → ℤ → ℤ → ℤ → ℂ) :
    (mkBox (H := H) P hU W α β).tube = P.box := by
  -- Unfold the wiring and use the “box as tube” lemma from `BGTypeIIData`.
  simpa [mkBox, Data.tube, Data.C] using
    (SSU.Engines.BGTypeII.TubeParams.tubeFinset_boxTube_eq_box (P := P) hU)

/-- The Type–II array `F(d,n)` on the tube (TeX: `α⊗β` with cutoff `W`). -/
noncomputable def F (f : H) (i j : ℤ) : TubePoint → ℂ :=
  (D.C).F f i j

/-- Aggregated coefficients `A_k := ∑_{dn=k} F(d,n)` (TeX Eq. (5.2)). -/
noncomputable def A (f : H) (i j k : ℤ) : ℂ :=
  coeffByProd (D.tube) (D.F f i j) k

/-!
## Product exponential sum on the torus

TeX writes `S(ξ) = ∑_k A_k e(ξ k / X)`. On `𝕋 = AddCircle 1`, the standard character is
`fourier k : 𝕋 → ℂ`, so the canonical “unscaled” torus version is

`S(x) = ∑_k A_k * fourier k x`.

If you want the TeX scaling `ξ/X`, use `x := (ξ / X : ℝ)` as a torus element and evaluate `S x`.
-/

/--
The product exponential sum in the **real-frequency** variable `ξ` (TeX normalization):

`S(ξ) := ∑_{p ∈ tube} F(p) e(ξ * prod(p) / X)`.
-/
noncomputable def prodSumReal (X ξ : ℝ) (f : H) (i j : ℤ) : ℂ :=
  SSU.Engines.TypeII.ProductToeplitz.prodSum X ξ D.tube (D.F f i j)

/--
The grouped-by-product form (real-frequency):

`S(ξ) = ∑_{k ∈ tube.image prod} A_k e(ξ k / X)`.

This is the TeX “group by product” rewrite of the Type–II sum.
-/
noncomputable def prodSumRealByProd (X ξ : ℝ) (f : H) (i j : ℤ) : ℂ :=
  ∑ k ∈ (D.tube).image prod, (D.A f i j k) * SSU.Engines.TypeII.e (ξ * (k : ℝ) / X)

theorem prodSumReal_eq_prodSumRealByProd (X ξ : ℝ) (f : H) (i j : ℤ) :
    D.prodSumReal X ξ f i j = D.prodSumRealByProd X ξ f i j := by
  classical
  -- This is exactly `ProductToeplitz.prodSum_eq_sum_image_prod`.
  simpa [Data.prodSumReal, Data.prodSumRealByProd, Data.A] using
    (SSU.Engines.TypeII.ProductToeplitz.prodSum_eq_sum_image_prod
      (X := X) (ξ := ξ) (T := D.tube) (F := D.F f i j))

/-- The product exponential sum on `𝕋`: `S(x) := ∑_{p∈tube} F(p) * fourier (prod p) x`. -/
noncomputable def prodSumTorus (f : H) (i j : ℤ) (x : UC) : ℂ :=
  ∑ p ∈ D.tube, (D.F f i j p) * (fourier (T := (1 : ℝ)) (prod p) x)

/-- Fiber sum defining `A_k` as an explicit filtered sum. -/
noncomputable def A' (f : H) (i j k : ℤ) : ℂ :=
  ∑ p ∈ D.tube with prod p = k, D.F f i j p

theorem A_eq_A' (f : H) (i j k : ℤ) : D.A f i j k = D.A' f i j k := by
  classical
  -- `coeffByProd_eq_sum_filter` is exactly this statement.
  simpa [Data.A, Data.A'] using (coeffByProd_eq_sum_filter (T := D.tube) (F := D.F f i j) k)

/-- The grouped-by-product form: `S(x) = ∑_{k} A_k * fourier k x` (finite sum over `tube.image prod`). -/
noncomputable def prodSumTorusByProd (f : H) (i j : ℤ) (x : UC) : ℂ :=
  ∑ k ∈ (D.tube).image prod, (D.A f i j k) * (fourier (T := (1 : ℝ)) k x)

theorem prodSumTorus_eq_prodSumTorusByProd (f : H) (i j : ℤ) (x : UC) :
    D.prodSumTorus f i j x = D.prodSumTorusByProd f i j x := by
  classical
  -- Group the sum over `tube` by the map `prod : TubePoint → ℤ`.
  let w : TubePoint → ℂ := fun p => (D.F f i j p) * (fourier (T := (1 : ℝ)) (prod p) x)
  have hfib :
      (∑ k ∈ (D.tube).image prod, ∑ p ∈ D.tube with prod p = k, w p) = ∑ p ∈ D.tube, w p := by
    simpa [w] using
      (Finset.sum_fiberwise_of_maps_to (s := D.tube) (t := (D.tube).image prod) (g := prod)
        (h := fun p hp => Finset.mem_image_of_mem prod hp) (f := w))
  -- Compute each fiber sum at fixed `k`.
  have hfiber (k : ℤ) :
      (∑ p ∈ D.tube with prod p = k, w p) = (D.A' f i j k) * (fourier (T := (1 : ℝ)) k x) := by
    -- On the fiber `prod p = k`, the character is constant `fourier k x`.
    have hrewrite :
        (∑ p ∈ D.tube with prod p = k, w p)
          =
        ∑ p ∈ D.tube with prod p = k, (D.F f i j p) * (fourier (T := (1 : ℝ)) k x) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hpk : prod p = k := (Finset.mem_filter.mp hp).2
      simp [w, hpk]
    -- Pull out the constant factor.
    have hpull :
        (∑ p ∈ D.tube with prod p = k, (D.F f i j p) * (fourier (T := (1 : ℝ)) k x))
          =
        (∑ p ∈ D.tube with prod p = k, D.F f i j p) * (fourier (T := (1 : ℝ)) k x) := by
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
        (Finset.mul_sum (s := (D.tube).filter (fun p => prod p = k))
          (f := fun p => D.F f i j p) (a := (fourier (T := (1 : ℝ)) k x : ℂ))).symm
    simpa [Data.A', Finset.sum_filter, Finset.sum_mul] using (hrewrite.trans hpull)
  -- Substitute the fiber computation into `hfib`.
  have hgroup :
      (∑ p ∈ D.tube, w p)
        =
      ∑ k ∈ (D.tube).image prod, (D.A' f i j k) * (fourier (T := (1 : ℝ)) k x) := by
    -- Rewrite the LHS using `hfib`, then simplify each fiber.
    have := hfib.symm
    -- `simp` each fiber using `hfiber`.
    refine this.trans ?_
    refine Finset.sum_congr rfl ?_
    intro k hk
    simpa using (hfiber (k := k))
  -- Replace `A'` by `A` and unfold `prodSumTorus`/`prodSumTorusByProd`.
  have hA : ∀ k : ℤ, D.A f i j k = D.A' f i j k := by
    intro k
    simpa using (D.A_eq_A' (f := f) (i := i) (j := j) (k := k))
  -- Finish by rewriting `prodSumTorus` and `prodSumTorusByProd` into the normalized forms.
  calc
    D.prodSumTorus f i j x = ∑ p ∈ D.tube, w p := by
      simp [Data.prodSumTorus, w]
    _ = ∑ k ∈ (D.tube).image prod, (D.A' f i j k) * (fourier (T := (1 : ℝ)) k x) := hgroup
    _ = ∑ k ∈ (D.tube).image prod, (D.A f i j k) * (fourier (T := (1 : ℝ)) k x) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [hA k]
    _ = D.prodSumTorusByProd f i j x := by
      simp [Data.prodSumTorusByProd]

/-!
### Deterministic bridge: real-frequency form ↔ torus character

This is just notational: `e(ξ k / X)` equals `fourier k ((ξ/X) : 𝕋)` by `fourier_coe_eq_e`.
-/

theorem e_eq_fourier_coe (X ξ : ℝ) (k : ℤ) :
    SSU.Engines.TypeII.e (ξ * (k : ℝ) / X)
      =
    (fourier (T := (1 : ℝ)) k ((ξ / X : ℝ) : UC) : ℂ) := by
  -- `AddCircle.fourier_coe_apply`: explicit formula for `fourier` on real representatives.
  -- With `T = 1`, `fourier k (x : UC) = exp (2π i * k * x)`.
  have hfour :
      (fourier (T := (1 : ℝ)) k ((ξ / X : ℝ) : UC) : ℂ)
        =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℝ) * (ξ / X)) := by
    -- `AddCircle.fourier_coe_apply` is stated with `n : ℤ`; coerce `k` to `ℝ` as needed.
    simpa [Real.pi, one_div] using
      (AddCircle.fourier_coe_apply (T := (1 : ℝ)) (n := k) (x := (ξ / X)))
  -- Rewrite `e` and match the exponents.
  have hmul : ξ * (k : ℝ) / X = (k : ℝ) * (ξ / X) := by ring
  -- `TypeII.e t = exp (2π i t)`.
  unfold SSU.Engines.TypeII.e
  -- Convert `hfour` to the desired direction.
  simpa [hmul, mul_assoc, mul_left_comm, mul_comm] using hfour.symm

theorem prodSumRealByProd_eq_prodSumTorusByProd (X ξ : ℝ) (f : H) (i j : ℤ) :
    D.prodSumRealByProd X ξ f i j = D.prodSumTorusByProd f i j ((ξ / X : ℝ) : UC) := by
  classical
  unfold Data.prodSumRealByProd Data.prodSumTorusByProd
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [e_eq_fourier_coe (X := X) (ξ := ξ) (k := k), mul_assoc]

end Data

end

end BGTypeIIArray
end Engines
end SSU
