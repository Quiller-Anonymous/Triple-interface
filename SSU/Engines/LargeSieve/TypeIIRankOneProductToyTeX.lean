import SSU.Engines.TypeII
import SSU.Engines.LargeSieve.RankOneShearLargeSieveTeX

/-!
Toy-but-nontrivial rank-one Type–II extraction in *shear coordinates* (TeX-flavored).

This file provides a concrete decomposition for `typeIISum` in the easiest “identity shear” case
`(a,q) = (0,1)`:

* `shearU 0 1 (d,n) = n`, `shearV (d,n) = d`,
* so the phase is exactly `e((ξ/X) * n * d)`,
* and on a product index set `V × U` with separated coefficients
  `F(d,n) = α(d) * β(n)`,
  the oscillatory sum is a rank-one signal
  `∑_{u∈U} β(u) * ∑_{v∈V} α(v) e(t*u*v)`, with `t = ξ/X`.

This is the first place where the proved MV machinery can be applied *directly* to a `typeIISum`
statement without any additional tube geometry.

Downstream, the real SSU extraction will replace this toy `(a,q)=(0,1)` decomposition by the
TeX shearing map and congruence bookkeeping, but the algebraic proof shape is the same.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex

namespace RankOneProductToy

/-- In the identity-shear case `(a,q) = (0,1)`, on a product set `V × U` with separated
coefficients `F(d,n) = α(d) * β(n)`, the Type–II sum is literally a rank-one exponential signal. -/
theorem typeIISum_eq_rankOneSignal
    (X ξ : ℝ) (U V : Finset ℤ) (α β : ℤ → ℂ) :
    typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) X ξ (V.product U) (fun p => α p.1 * β p.2)
      =
    ∑ u ∈ U,
      β u * (∑ v ∈ V, α v * e ((ξ / X) * (u : ℝ) * (v : ℝ))) := by
  classical
  -- Work from the LHS only (so we don't accidentally rewrite the RHS into a different phase form).
  calc
    typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) X ξ (V.product U) (fun p => α p.1 * β p.2)
        =
      ∑ v ∈ V, ∑ u ∈ U,
        (α v * β u) * e ((ξ / X) * (u : ℝ) * (v : ℝ)) := by
          -- Expand `typeIISum` over the product set and normalize the phase.
          -- (`shearU 0 1 (v,u) = u`, `shearV (v,u) = v`, and `/ (1*X)` becomes `/X`.)
          simp [typeIISum, shearU, shearV, Finset.sum_product, div_eq_mul_inv,
            mul_assoc, mul_left_comm, mul_comm]
    _ =
      ∑ u ∈ U, ∑ v ∈ V, (α v * β u) * e ((ξ / X) * (u : ℝ) * (v : ℝ)) := by
          simpa using (Finset.sum_comm (s := V) (t := U)
            (f := fun v u => (α v * β u) * e ((ξ / X) * (u : ℝ) * (v : ℝ))))
    _ =
      ∑ u ∈ U, β u * (∑ v ∈ V, α v * e ((ξ / X) * (u : ℝ) * (v : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          -- Factor `β u` out of the inner sum.
          calc
            (∑ v ∈ V, (α v * β u) * e ((ξ / X) * (u : ℝ) * (v : ℝ)))
                =
              ∑ v ∈ V, β u * (α v * e ((ξ / X) * (u : ℝ) * (v : ℝ))) := by
                refine Finset.sum_congr rfl ?_
                intro v hv
                ring_nf
            _ = β u * (∑ v ∈ V, α v * e ((ξ / X) * (u : ℝ) * (v : ℝ))) := by
                simp [Finset.mul_sum, mul_assoc]

/-!
### A TeX-friendly version (interval index sets)

To apply the MV inequality *directly*, we keep the inner index set as an actual interval `Icc`.
This matches how the real SSU Step 3/4 pipeline uses interval-like `zBox` sets.
-/

theorem typeIISum_eq_rankOneSignal_Icc
    (X ξ : ℝ) (U : Finset ℤ) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) X ξ
        ((Finset.Icc a (a + (N : ℤ) - 1)).product U) (fun p => α p.1 * β p.2)
      =
    ∑ u ∈ U,
      β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        α v * e ((ξ / X) * (u : ℝ) * (v : ℝ))) := by
  simpa using
    (typeIISum_eq_rankOneSignal (X := X) (ξ := ξ) (U := U)
      (V := (Finset.Icc a (a + (N : ℤ) - 1))) (α := α) (β := β))

theorem norm_typeIISum_sq_le_one_add_log_Icc
    (X ξ : ℝ) (U : Finset ℤ) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (R : ℕ)
    (hDist : ∀ i ∈ U, ∀ j ∈ U, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / X)| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / X ≠ 0) :
    ‖typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) X ξ
        ((Finset.Icc a (a + (N : ℤ) - 1)).product U) (fun p => α p.1 * β p.2)‖ ^ 2
      ≤
    (∑ u ∈ U, ‖β u‖ ^ 2) *
      ((N : ℝ) + (1 / |(ξ / X)|) * (1 + Real.log R)) *
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
  classical
  have hdecomp :=
    typeIISum_eq_rankOneSignal_Icc (X := X) (ξ := ξ) (U := U) (a := a) (N := N) (α := α) (β := β)
  -- Reduce to the rank-one MV lemma via the decomposition.
  have h :=
    SSU.Engines.LargeSieve.RankOneShear.norm_rankOneSignal_sq_le_one_add_log
      (J := U) (R := R) (hDist := hDist) (t := (ξ / X)) (ht := ht) (ht0 := ht0)
      (a := a) (N := N) (α := α) (β := β)
  -- Rewrite the goal using the decomposition, then apply the rank-one bound.
  -- (`rw` avoids any mismatch between `product` and `×ˢ` notation.)
  rw [hdecomp]
  simpa using h

end RankOneProductToy

end

end LargeSieve
end TypeII
end Engines
end SSU
