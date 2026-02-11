import SSU.Engines.LargeSieve.TypeIIStep4Reduce
import SSU.Engines.LargeSieve.RankOneShearLargeSieveTeX

/-!
Apply MV large sieve to TeX Step 4 **assuming rank-one shear coefficients**.

This is the `v`-analogue of `SSU/Engines/LargeSieve/TypeIIStep3RankOneApplyMVTeX.lean`.

Deterministic: `typeIISum = ∑_v phase(v) * innerSumVZ(v)` (already proved).
Rank-one hypothesis: `innerSumVZ(v) = β(v) * ∑_{z∈Icc} α(z) e((ξ/X) v z)`.
Analytic: MV large sieve bounds the resulting rank-one exponential sum.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex

namespace Step4RankOne

open SSU.Engines.TypeII

/-- MV bound for `typeIISum` in the Step 4 decomposition, assuming `innerSumVZ` is rank-one in `v`.

The phase factor in `typeIISum_eq_outer_v_innerVZ` is unimodular and is absorbed into `β`.
-/
theorem norm_typeIISum_sq_le_one_add_log_of_rankOne_innerSumVZ
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (a : ℤ) (N : ℕ) (α β : ℤ → ℂ)
    (R : ℕ)
    (hDist : ∀ i ∈ vSet td, ∀ j ∈ vSet td, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / td.X)| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / td.X ≠ 0)
    (hRankOne :
      ∀ v : ℤ, v ∈ vSet td →
        innerSumVZ td ξ F v
          =
        β v * (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
          α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ)))) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (∑ v ∈ vSet td, ‖β v‖ ^ 2) *
      ((N : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log R)) *
      (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
  classical
  -- Deterministic Step 4 decomposition of `typeIISum`.
  have hdecomp0 := typeIISum_eq_outer_v_innerVZ (td := td) (ξ := ξ) (F := F)
  -- Rewrite `typeIISum` using the rank-one hypothesis on `innerSumVZ`.
  have hdecomp :
      typeIISum td.a td.q td.X ξ td.T F
        =
      ∑ v ∈ vSet td,
        (β v * e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
          (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
            α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ))) := by
    rw [hdecomp0]
    refine Finset.sum_congr rfl ?_
    intro v hv
    have hv' := hRankOne v hv
    -- commute the unimodular phase into `β`.
    simpa [hv', mul_assoc, mul_left_comm, mul_comm]

  -- Absorb the unimodular factor into `β`.
  let β' : ℤ → ℂ :=
    fun v => β v * e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))
  have hβ' :
      (∑ v ∈ vSet td, ‖β' v‖ ^ 2) = ∑ v ∈ vSet td, ‖β v‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    simp [β', norm_mul, norm_e]

  have hMV :
      ‖∑ v ∈ vSet td,
          β' v * (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
            α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ)))‖ ^ 2
        ≤
      (∑ v ∈ vSet td, ‖β v‖ ^ 2) *
        ((N : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log R)) *
        (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := by
    have h :=
      SSU.Engines.LargeSieve.RankOneShear.norm_rankOneSignal_sq_le_one_add_log
        (J := vSet td) (R := R) (hDist := hDist) (t := (ξ / td.X))
        (ht := ht) (ht0 := ht0) (a := a) (N := N) (α := α) (β := β')
    simpa [hβ'] using h

  have hnorm :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        =
      ‖∑ v ∈ vSet td,
          β' v * (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
            α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ)))‖ ^ 2 := by
    have hnorm0 := congrArg (fun g => ‖g‖ ^ 2) hdecomp
    have hsum :
        (∑ v ∈ vSet td,
            (β v * e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
              (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
                α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ))))
          =
        (∑ v ∈ vSet td,
            β' v *
              (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
                α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ)))) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simp [β', mul_assoc, mul_left_comm, mul_comm]
    simpa [hsum] using hnorm0

  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        =
        ‖∑ v ∈ vSet td,
            β' v * (∑ z ∈ (Finset.Icc a (a + (N : ℤ) - 1)),
              α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ)))‖ ^ 2 := hnorm
    _ ≤
        (∑ v ∈ vSet td, ‖β v‖ ^ 2) *
          ((N : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log R)) *
          (∑ k ∈ (Finset.univ : Finset (Fin N)), ‖α (a + (k : ℕ))‖ ^ 2) := hMV

end Step4RankOne

end

end LargeSieve
end TypeII
end Engines
end SSU

