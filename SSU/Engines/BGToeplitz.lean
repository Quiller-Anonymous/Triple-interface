import SSU.Engines.TypeII

/-!
05_BG.tex (BG) — Toeplitz-in-product bookkeeping block.

This file mirrors the “Bilinear form, short–shift operator, and goal” subsection at the level of
the *Toeplitz-in-product* viewpoint:

* define `A_k := ∑_{dn=k} α_d β_n W(d/D,n/N)` as a product-fiber sum;
* rewrite the oscillatory sum `S(ξ) = ∑_{d,n} α_d β_n W(...) e(ξ dn / X)` as `∑_k A_k e(ξ k / X)`.

This is the deterministic algebraic part needed before any large-sieve / Type-II analytic bounds.
It does **not** attempt to prove the full “quadratic form equals ∑_{k,k'} … K(k'-k)” identity;
for the SSU Toeplitz route we instead use the already-proved Fourier insertion identity
`ProductToeplitz.tubeFormProd_eq` together with the regrouping of `prodSum`.
-/

namespace SSU
namespace Engines
namespace BGToeplitz

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII
open SSU.Engines.TypeII.ProductToeplitz

/-!
## Data matching (5.2)

We keep the coefficient arrays abstract. The only “structural” ingredient here is that we are
summing over a finite tube set `T : Finset (ℤ×ℤ)`.
-/

structure CoeffData where
  X : ℝ
  /-- Tube lattice points `(d,n)`. -/
  T : Finset TubePoint
  /-- Coefficients `α_d`. -/
  α : ℤ → ℂ
  /-- Coefficients `β_n`. -/
  β : ℤ → ℂ
  /-- Weight `W(d,n)` (TeX: `W(d/D,n/N)`). -/
  W : TubePoint → ℂ

namespace CoeffData

variable (D : CoeffData)

/-- Type-II array `F(d,n) = α_d β_n W(d,n)` (TeX: `α⊗β` with a cutoff `W`). -/
noncomputable def F : TubePoint → ℂ :=
  fun p => D.α p.1 * D.β p.2 * D.W p

/-- Tube coefficients `A_k := ∑_{dn=k} α_d β_n W(d,n)` (TeX equation (5.2)). -/
noncomputable def A (k : ℤ) : ℂ :=
  coeffByProd D.T (D.F) k

theorem A_eq_sum_filter (k : ℤ) :
    D.A k = ∑ p ∈ D.T with prod p = k, D.F p := by
  simpa [CoeffData.A, CoeffData.F] using
    (coeffByProd_eq_sum_filter (T := D.T) (F := D.F) k)

/-!
## Toeplitz quadratic form regrouping (TeX line-34 “group by product”)

TeX also rewrites the Toeplitz-in-product quadratic form

`∑_{p,q∈T} F(p) K(prod(q)-prod(p)) conj(F(q))`

as a double sum over the product variable `k = d n` via the aggregated coefficients `A_k`.

We record both:

* the “direct” grouping lemma matching our definition of `tubeFormProd`, and
* the TeX ordering `A_{k'} \overline{A_k} K(k'-k)` (05_BG.tex line 37), which follows from the
  direct lemma after swapping dummy indices and using that `K` is even in the BG setup.
-/

theorem tubeFormProd_eq_sum_A (K : ℤ → ℝ) :
    tubeFormProd K D.T D.F =
      ∑ k ∈ D.T.image prod, ∑ k' ∈ D.T.image prod,
        (D.A k) * (K (k' - k)) * star (D.A k') := by
  simpa [CoeffData.A, CoeffData.F] using
    (ProductToeplitz.tubeFormProd_eq_sum_image_prod (K := K) (T := D.T) (F := D.F))

theorem tubeFormProd_eq_sum_A_tex (K : ℤ → ℝ) (hK : ∀ t : ℤ, K (-t) = K t) :
    tubeFormProd K D.T D.F =
      ∑ k ∈ D.T.image prod, ∑ k' ∈ D.T.image prod,
        (D.A k') * star (D.A k) * (K (k' - k)) := by
  classical
  -- Start from the “direct” regrouping lemma, then swap indices and use evenness of `K`.
  have h1 := D.tubeFormProd_eq_sum_A (K := K)
  -- Introduce the product-index finset once (to keep rewriting localized).
  let S : Finset ℤ := D.T.image prod
  have h1' :
      tubeFormProd K D.T D.F =
        ∑ k ∈ S, ∑ k' ∈ S, (D.A k) * (K (k' - k)) * star (D.A k') := by
    simpa [S] using h1
  -- Convert both the “direct” grouped sum and the TeX-ordered sum into sums over `S × S`,
  -- and then reindex by swapping the pair.
  rw [h1']
  -- Replace the RHS product-index finset by `S` (definitional).
  change
    (∑ k ∈ S, ∑ k' ∈ S, D.A k * (K (k' - k)) * star (D.A k')) =
      ∑ k ∈ S, ∑ k' ∈ S, D.A k' * star (D.A k) * (K (k' - k))
  have hdir :
      (∑ k ∈ S, ∑ k' ∈ S, (D.A k) * (K (k' - k)) * star (D.A k'))
        =
      ∑ kk ∈ S.product S, (D.A kk.1) * (K (kk.2 - kk.1)) * star (D.A kk.2) := by
    simp [Finset.sum_product, mul_assoc, mul_left_comm, mul_comm]
  have htex :
      (∑ k ∈ S, ∑ k' ∈ S, (D.A k') * star (D.A k) * (K (k' - k)))
        =
      ∑ kk ∈ S.product S, (D.A kk.2) * star (D.A kk.1) * (K (kk.2 - kk.1)) := by
    simp [Finset.sum_product, mul_assoc, mul_left_comm, mul_comm]
  -- Reduce to an equality of two sums over `S.product S`.
  rw [hdir, htex]
  -- Reindex the `S × S` sum by swapping coordinates, and use evenness of `K`.
  refine Finset.sum_bij
      (s := S.product S) (t := S.product S)
      (f := fun kk => (D.A kk.1) * (K (kk.2 - kk.1)) * star (D.A kk.2))
      (g := fun kk => (D.A kk.2) * star (D.A kk.1) * (K (kk.2 - kk.1)))
      (i := fun kk _ => (kk.2, kk.1))
      (hi := ?_) (i_inj := ?_) (i_surj := ?_) (h := ?_)
  · intro kk hkk
    rcases Finset.mem_product.mp hkk with ⟨hk1, hk2⟩
    exact Finset.mem_product.mpr ⟨hk2, hk1⟩
  · intro a ha b hb hab
    cases a with
    | mk a1 a2 =>
      cases b with
      | mk b1 b2 =>
        cases hab
        rfl
  · intro kk hkk
    refine ⟨(kk.2, kk.1), ?_, rfl⟩
    rcases Finset.mem_product.mp hkk with ⟨hk1, hk2⟩
    exact Finset.mem_product.mpr ⟨hk2, hk1⟩
  · intro kk hkk
    -- Compare the term at `kk` with the target term at `swap kk`.
    have hK' : K (kk.1 - kk.2) = K (kk.2 - kk.1) := by
      have : -(kk.2 - kk.1) = kk.1 - kk.2 := by abel
      simpa [this] using (hK (kk.2 - kk.1))
    -- Unfold `i` and simplify; use commutativity in `ℂ`.
    simp [hK', mul_assoc, mul_left_comm, mul_comm]

/-!
## Oscillatory sum regrouping

This is the “group by product” identity applied to the BG coefficient array.
-/

theorem prodSum_eq_sum_A (ξ : ℝ) :
    prodSum D.X ξ D.T D.F =
      ∑ k ∈ D.T.image prod, (D.A k) * e (ξ * (k : ℝ) / D.X) := by
  -- This is the generic regrouping lemma `prodSum_eq_sum_image_prod`.
  simpa [CoeffData.A, CoeffData.F] using
    (prodSum_eq_sum_image_prod (X := D.X) (ξ := ξ) (T := D.T) (F := D.F))

end CoeffData

end

end BGToeplitz
end Engines
end SSU
