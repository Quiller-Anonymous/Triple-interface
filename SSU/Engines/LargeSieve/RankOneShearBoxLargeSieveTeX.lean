import SSU.Engines.LargeSieve.TypeIIShearSumTeX
import SSU.Engines.LargeSieve.RankOneShearLargeSieveTeX

/-!
TeX Step 3/4 large-sieve bound for a **rank-one shear box**.

This is the clean “first real” analytic lemma for the large-sieve stage:

* we work directly with the TeX shear sum `shearSum`,
* we assume coefficients factor as `F(u,v) = β(u) α(v)` on a product set
  `J × {a, a+1, ..., a+(N-1)}`,
* we apply the proved Montgomery–Vaughan large sieve (packaged in
  `RankOneShearLargeSieveTeX`) to obtain a TeX-friendly polylog bound, and
* we rewrite the RHS in terms of the 2D `ℓ²` energy `boxEnergy`.

This lemma is meant to be used **before** any tube restriction: restricting support can only
decrease the energy.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex

namespace RankOneShearBox

open SSU.Engines.LargeSieve.RankOneShear

/-- The rank-one shear box set `J × Icc(a, a+N-1)` as a finset of shear points. -/
def box (J : Finset ℤ) (a : ℤ) (N : ℕ) : Finset ShearPoint :=
  J.product (Finset.Icc a (a + (N : ℤ) - 1))

@[simp] theorem mem_box_iff (J : Finset ℤ) (a : ℤ) (N : ℕ) (uv : ShearPoint) :
    uv ∈ box J a N ↔ uv.1 ∈ J ∧ uv.2 ∈ (Finset.Icc a (a + (N : ℤ) - 1)) := by
  simp [box]

/-- On a rank-one shear box, `shearSum` is exactly the rank-one signal sum used by MV. -/
theorem shearSum_eq_rankOneSignal
    (q : ℤ) (X ξ : ℝ) (J : Finset ℤ) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    shearSum q X ξ (box J a N) (fun uv => β uv.1 * α uv.2)
      =
    ∑ u ∈ J,
      β u *
        (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := by
  classical
  -- Expand the product finset sum and pull out the outer factor `β u`.
  have hphase (u v : ℤ) :
      SSU.Engines.TypeII.e (ξ * ((u : ℝ) * (v : ℝ)) / ((q : ℝ) * X))
        =
      SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ)) := by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- Rewrite `shearSum` on the product set as an iterated sum.
  unfold shearSum box
  -- Outer/inner sums over `J × I`.
  simp [Finset.sum_product]
  -- Now factor `β u` out of the inner sum and rewrite the phase using `hphase`.
  refine Finset.sum_congr rfl ?_
  intro u hu
  -- Rewrite the phase inside the `e` factor, pointwise in `v`, and reassociate the products so
  -- we can pull out the constant `β u`.
  have hrew :
      (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          β u * α v * SSU.Engines.TypeII.e (ξ * (u : ℝ) * (v : ℝ) / ((q : ℝ) * X)))
        =
      ∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          β u * (α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    -- reassociate `β u * α v * e(…)` into `β u * (α v * e(…))` and rewrite the phase
    simp [mul_assoc, hphase u v]
  calc
    (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        β u * α v * SSU.Engines.TypeII.e (ξ * (u : ℝ) * (v : ℝ) / ((q : ℝ) * X)))
        =
      ∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        β u * (α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := hrew
    _ =
      β u * (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
        α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ))) := by
      -- Pull out the constant factor `β u` using `Finset.mul_sum`.
      simpa [Finset.mul_sum] using
        (Finset.mul_sum (a := β u)
          (s := (Finset.Icc a (a + (N : ℤ) - 1)))
          (f := fun v : ℤ =>
            α v * SSU.Engines.TypeII.e ((ξ / ((q : ℝ) * X)) * (u : ℝ) * (v : ℝ)))).symm

/-- MV large-sieve bound for the TeX shear sum on a rank-one box, with RHS written as `boxEnergy`. -/
theorem norm_shearSum_sq_le_one_add_log_boxEnergy
    (q : ℤ) (X ξ : ℝ) (J : Finset ℤ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / ((q : ℝ) * X))| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box J a N) (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log R)) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy J a N α β := by
  classical
  -- Rewrite `shearSum` as the MV-ready rank-one signal.
  have hrew :=
    shearSum_eq_rankOneSignal (q := q) (X := X) (ξ := ξ) (J := J) (a := a) (N := N)
      (α := α) (β := β)
  -- Apply the MV bound in box-energy form.
  have hMV :=
    SSU.Engines.LargeSieve.RankOneShear.norm_rankOneSignal_sq_le_one_add_log_boxEnergy
      (J := J) (R := R) (hDist := hDist)
      (t := (ξ / ((q : ℝ) * X))) (ht := ht) (ht0 := ht0)
      (a := a) (N := N) (α := α) (β := β)
  simpa [hrew] using hMV

/-- Convenience specialization of `norm_shearSum_sq_le_one_add_log_boxEnergy` to an interval
`J = Icc A B`, using the deterministic diameter bound `distZ ≤ toNat (B-A)`. -/
theorem norm_shearSum_sq_le_one_add_log_boxEnergy_Icc
    (q : ℤ) (X ξ : ℝ) (A B : ℤ)
    (ht : |(ξ / ((q : ℝ) * X))| * (Int.toNat (B - A) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / ((q : ℝ) * X) ≠ 0)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    ‖shearSum q X ξ (box (Finset.Icc A B) a N) (fun uv => β uv.1 * α uv.2)‖ ^ 2
      ≤
    ((N : ℝ) + (1 / |(ξ / ((q : ℝ) * X))|) * (1 + Real.log (Int.toNat (B - A)))) *
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy (Finset.Icc A B) a N α β := by
  classical
  have hDist :
      ∀ i ∈ (Finset.Icc A B), ∀ j ∈ (Finset.Icc A B),
        SSU.Hilbert.distZ i j ≤ Int.toNat (B - A) := by
    intro i hi j hj
    exact SSU.Hilbert.distZ_le_toNat_sub_of_mem_Icc (A := A) (B := B) (i := i) (j := j) hi hj
  simpa using
    (norm_shearSum_sq_le_one_add_log_boxEnergy
      (q := q) (X := X) (ξ := ξ) (J := Finset.Icc A B) (R := Int.toNat (B - A))
      (hDist := hDist) (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α) (β := β))

/-!
### Energy on a shear box

This is a small deterministic helper: it relates the literal `ℓ²` energy on the product finset
`box J a N` to the packaged `RankOneShear.boxEnergy` definition (which uses `Fin N` indexing).
-/

private theorem sum_Icc_eq_sum_univ_Fin (a : ℤ) (N : ℕ) (f : ℤ → ℝ) :
    (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)), f v)
      =
    ∑ k ∈ (Finset.univ : Finset (Fin N)), f (a + (k : ℕ)) := by
  classical
  -- First rewrite the `Icc` sum as a `range` sum.
  have hNat : ((a + (N : ℤ) - 1 + 1 - a)).toNat = N := by simp
  have hIcc :
      (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)), f v)
        =
      ∑ n ∈ Finset.range N, f (a + n) := by
    simpa [SSU.Engines.LargeSieve.MV.sum_Icc_eq_sum_range, hNat, add_assoc, add_left_comm, add_comm] using
      (SSU.Engines.LargeSieve.MV.sum_Icc_eq_sum_range (a := a) (b := a + (N : ℤ) - 1) (f := f))
  -- Convert `range N` to `Fin N`.
  let g : Fin N → ℝ := fun k => f (a + (k : ℕ))
  have hRange :
      (∑ n ∈ Finset.range N, f (a + n)) = ∑ k : Fin N, g k := by
    -- `sum_fin_eq_sum_range` gives a `range` sum with an `if`; simplify it on `range N`.
    have h0 := (Finset.sum_fin_eq_sum_range (n := N) (c := g))
    have h1 :
        (∑ k : Fin N, g k) = ∑ x ∈ Finset.range N, f (a + x) := by
      refine h0.trans ?_
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxlt : x < N := Finset.mem_range.1 hx
      simp [g, hxlt]
    exact h1.symm
  have huniv : (∑ k ∈ (Finset.univ : Finset (Fin N)), g k) = ∑ k : Fin N, g k := by simp
  -- Finish.
  calc
    (∑ v ∈ (Finset.Icc a (a + (N : ℤ) - 1)), f v)
        = ∑ n ∈ Finset.range N, f (a + n) := hIcc
    _ = ∑ k : Fin N, g k := hRange
    _ = ∑ k ∈ (Finset.univ : Finset (Fin N)), g k := by simpa [huniv]
    _ = ∑ k ∈ (Finset.univ : Finset (Fin N)), f (a + (k : ℕ)) := by simp [g]

theorem sum_norm_sq_on_box_eq_boxEnergy
    (J : Finset ℤ) (a : ℤ) (N : ℕ) (α β : ℤ → ℂ) :
    (∑ uv ∈ box J a N, ‖β uv.1 * α uv.2‖ ^ 2)
      =
    SSU.Engines.LargeSieve.RankOneShear.boxEnergy J a N α β := by
  classical
  unfold SSU.Engines.LargeSieve.RankOneShear.boxEnergy box
  -- Expand the product sum and rewrite the `Icc`-energy using `Fin N`.
  simp [Finset.sum_product, sum_Icc_eq_sum_univ_Fin (a := a) (N := N),
    mul_assoc, mul_left_comm, mul_comm]

end RankOneShearBox

end

end LargeSieve
end TypeII
end Engines
end SSU
