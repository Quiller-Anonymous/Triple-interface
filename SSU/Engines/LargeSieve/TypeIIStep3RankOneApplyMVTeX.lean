import SSU.Engines.LargeSieve.TypeIIStep3Reduce
import SSU.Engines.LargeSieve.RankOneShearLargeSieveTeX
import SSU.Engines.LargeSieve.TypeIIIndexBounds

/-!
Apply MV large sieve to TeX Step 3 **assuming rank-one shear coefficients**.

This file isolates the clean analytic step:

*Deterministic*: `typeIISum = ∑_u phase(u) * innerSumUZ(u)` (already proved).
*Rank-one hypothesis*: `innerSumUZ(u) = β(u) * ∑_{z∈Icc} α(z) e((ξ/X) u z)`.
*Analytic*: MV large sieve bounds `‖∑_u β(u) * ∑_z α(z) e(t u z)‖²`.

This is TeX-faithful to `05b_SSU.tex` Step 3, where the “real work” is proving that the extracted
inner coefficients are independent of `u` (after fixing a residue class).

We do **not** prove that extraction here; we just provide the reusable implication.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex

namespace Step3RankOne

open SSU.Engines.TypeII

/-- MV bound for `typeIISum` in the Step 3 decomposition, assuming `innerSumUZ` is rank-one in `u`.

The phase factor in `typeIISum_eq_outer_u_innerUZ` is unimodular and is absorbed into `β`.
-/
theorem norm_typeIISum_sq_le_one_add_log_of_rankOne_innerSumUZ
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (R : ℕ)
    (hDist : ∀ i ∈ uSet td, ∀ j ∈ uSet td, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / td.X)| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / td.X ≠ 0)
    (hRankOne :
      ∀ u : ℤ, u ∈ uSet td →
        innerSumUZ td ξ F u
          =
        β u * (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ)))) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (∑ u ∈ uSet td, ‖β u‖ ^ 2) *
      ((N : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log R)) *
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
  classical
  -- Deterministic Step 3 decomposition of `typeIISum`.
  have hdecomp0 := typeIISum_eq_outer_u_innerUZ (td := td) (ξ := ξ) (F := F)
  -- Rewrite `typeIISum` using the rank-one hypothesis on `innerSumUZ`.
  have hdecomp :
      typeIISum td.a td.q td.X ξ td.T F
        =
      ∑ u ∈ uSet td,
        (β u * e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
          (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
            α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ))) := by
    -- Expand `typeIISum` as `∑ phase(u) * innerSumUZ(u)` and substitute `innerSumUZ`.
    -- Then reassociate the scalar factors.
    classical
    -- First rewrite `typeIISum`.
    rw [hdecomp0]
    refine Finset.sum_congr rfl ?_
    intro u hu
    -- Substitute the rank-one form of `innerSumUZ`.
    have hu' := hRankOne u hu
    -- `simp` inlines the substitution and reassociates.
    simpa [hu', mul_assoc, mul_left_comm, mul_comm]

  -- Apply MV to the rank-one sum, absorbing the unimodular factor into `β`.
  let β' : ℤ → ℂ :=
    fun u => β u * e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))
  have hβ' :
      (∑ u ∈ uSet td, ‖β' u‖ ^ 2) = ∑ u ∈ uSet td, ‖β u‖ ^ 2 := by
    classical
    refine Finset.sum_congr rfl ?_
    intro u hu
    simp [β', norm_mul, norm_e]

  have hMV :
      ‖∑ u ∈ uSet td,
          β' u * (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
            α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ)))‖ ^ 2
        ≤
      (∑ u ∈ uSet td, ‖β u‖ ^ 2) *
        ((N : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log R)) *
        (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
    -- Apply the TeX-friendly rank-one MV lemma on the abstract frequency set `uSet td`.
    have h :=
      SSU.Engines.LargeSieve.RankOneShear.norm_rankOneSignal_sq_le_one_add_log
        (J := uSet td) (R := R) (hDist := hDist) (t := (ξ / td.X))
        (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α) (β := β')
    -- Replace `β'` energy by `β` energy.
    simpa [hβ'] using h

  -- Transport across the decomposition `hdecomp`, folding the unimodular factor into `β'`.
  have hnorm :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        =
      ‖∑ u ∈ uSet td,
          β' u * (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
            α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ)))‖ ^ 2 := by
    have hnorm0 := congrArg (fun g => ‖g‖ ^ 2) hdecomp
    have hsum :
        (∑ u ∈ uSet td,
            (β u * e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
              (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
                α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ))))
          =
        (∑ u ∈ uSet td,
            β' u *
              (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
                α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ)))) := by
      classical
      refine Finset.sum_congr rfl ?_
      intro u hu
      simp [β', mul_assoc, mul_left_comm, mul_comm]
    -- Rewrite the RHS of `hnorm0` using `hsum`.
    simpa [hsum] using hnorm0

  -- Finish.
  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        =
        ‖∑ u ∈ uSet td,
            β' u * (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
              α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ)))‖ ^ 2 := hnorm
    _ ≤
        (∑ u ∈ uSet td, ‖β u‖ ^ 2) *
          ((N : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log R)) *
          (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := hMV

/-- Geometry-specialized variant of
`norm_typeIISum_sq_le_one_add_log_of_rankOne_innerSumUZ`, using the deterministic diameter bound
on `uSet td`. -/
theorem norm_typeIISum_sq_le_one_add_log_of_rankOne_innerSumUZ_geom
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (hU0 : 0 ≤ td.U)
    (ht :
      |(ξ / td.X)| * (2 * Int.toNat (Int.ceil td.U) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / td.X ≠ 0)
    (hRankOne :
      ∀ u : ℤ, u ∈ uSet td →
        innerSumUZ td ξ F u
          =
        β u * (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ)))) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (∑ u ∈ uSet td, ‖β u‖ ^ 2) *
      ((N : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U)))) *
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
  let R : ℕ := 2 * Int.toNat (Int.ceil td.U)
  have hDist : ∀ i ∈ uSet td, ∀ j ∈ uSet td, SSU.Hilbert.distZ i j ≤ R := by
    intro i hi j hj
    simpa [R] using
      (IndexBounds.distZ_le_two_mul_toNat_ceilU_on_uSet (td := td) (hU0 := hU0) i hi j hj)
  simpa [R] using
    (norm_typeIISum_sq_le_one_add_log_of_rankOne_innerSumUZ
      (td := td) (ξ := ξ) (F := F) (a := a) (N := N) (α := α) (β := β)
      (R := R) (hDist := hDist) (ht := by simpa [R] using ht) (ht0 := ht0)
      (hRankOne := hRankOne))

end Step3RankOne

end

end LargeSieve
end TypeII
end Engines
end SSU
