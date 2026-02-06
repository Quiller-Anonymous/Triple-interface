import SSU.Engines.BGToeplitzReduction

/-!
05_BG.tex — bilinear/Toeplitz normalization layer (deterministic).

This file introduces a TeX-named bilinear form that matches the BG “Toeplitz in the product”
presentation (after grouping by the product variable `k = d*n`), and relates it to the existing
`ProductToeplitz.tubeFormProd` definition used by the SSU Type–II Toeplitz bridge.

It does **not** perform the application-specific extraction of the Type–II coefficient array
`F(d,n)` from packet Grams; it only records the deterministic identities once such an `F` is given.
-/

namespace SSU
namespace Engines
namespace BGBilinear

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII
open SSU.Engines.TypeII.ProductToeplitz

/--
BG “Toeplitz in the product” bilinear form:

`⟪TF, G⟫ := ∑_{p∈T} ∑_{p'∈T} F(p') * conj(G(p)) * K(prod(p') - prod(p))`.

This is the normalization that corresponds to the TeX `k,k'`-shift variable once you have grouped
the 2D coefficients by `k = d*n`.
-/
def bilinearFormProd (K : ℤ → ℝ) (T : Finset TubePoint) (F G : TubePoint → ℂ) : ℂ :=
  ∑ p ∈ T, ∑ p' ∈ T, (F p') * star (G p) * (K (prodShift p p'))

theorem bilinearFormProd_eq_tubeFormProd
    (K : ℤ → ℝ) (hK : ∀ t : ℤ, K (-t) = K t) (T : Finset TubePoint) (F : TubePoint → ℂ) :
    bilinearFormProd K T F F = tubeFormProd K T F := by
  classical
  -- This is the deterministic swap `(p,p') ↦ (p',p)` plus the evenness of `K`:
  -- `prodShift p' p = -(prodShift p p')`.
  unfold bilinearFormProd tubeFormProd
  -- Rewrite both sides as sums over `T × T`.
  have hL :
      (∑ pp ∈ T.product T, (F pp.2) * star (F pp.1) * (K (prodShift pp.1 pp.2)))
        =
      (∑ p ∈ T, ∑ p' ∈ T, F p' * star (F p) * (K (prodShift p p'))) := by
    simp [Finset.sum_product]
  have hR :
      (∑ pp ∈ T.product T, (F pp.1) * (K (prodShift pp.1 pp.2)) * star (F pp.2))
        =
      (∑ p ∈ T, ∑ q ∈ T, F p * (K (prodShift p q)) * star (F q)) := by
    simp [Finset.sum_product]
  -- Replace the goal by an equality of two sums over `T.product T`.
  rw [← hL, ← hR]
  -- Reindex the LHS by swapping the pair.
  refine Finset.sum_bij
      (s := T.product T) (t := T.product T)
      (f := fun pp => (F pp.2) * star (F pp.1) * (K (prodShift pp.1 pp.2)))
      (g := fun pp => (F pp.1) * (K (prodShift pp.1 pp.2)) * star (F pp.2))
      (i := fun pp _ => (pp.2, pp.1))
      (hi := ?_) (i_inj := ?_) (i_surj := ?_) (h := ?_)
  · intro pp hpp
    rcases Finset.mem_product.mp hpp with ⟨hp1, hp2⟩
    exact Finset.mem_product.mpr ⟨hp2, hp1⟩
  · intro a ha b hb hab
    cases a with
    | mk a1 a2 =>
      cases b with
      | mk b1 b2 =>
        cases hab
        rfl
  · intro pp hpp
    refine ⟨(pp.2, pp.1), ?_, rfl⟩
    rcases Finset.mem_product.mp hpp with ⟨hp1, hp2⟩
    exact Finset.mem_product.mpr ⟨hp2, hp1⟩
  · intro pp hpp
    have hshift : prodShift pp.2 pp.1 = -(prodShift pp.1 pp.2) := by
      simp [prodShift, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hK' : K (prodShift pp.2 pp.1) = K (prodShift pp.1 pp.2) := by
      simpa [hshift] using (hK (prodShift pp.1 pp.2))
    -- Compare the term at `pp` with the target term at `swap pp`.
    -- Use evenness to rewrite the kernel and commutativity/associativity in `ℂ`.
    simp [hK', mul_assoc, mul_left_comm, mul_comm]

end

end BGBilinear
end Engines
end SSU
