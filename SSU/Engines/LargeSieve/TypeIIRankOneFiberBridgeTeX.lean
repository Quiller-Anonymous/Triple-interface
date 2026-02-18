import SSU.Engines.LargeSieve.TypeIIZBoxRewrite
import SSU.Engines.LargeSieve.TypeIIStep3RankOneApplyMVTeX
import SSU.Engines.LargeSieve.TypeIIStep4RankOneApplyMVTeX

/-!
Bridges from *fiber-level* rank-one hypotheses to the MV-ready rank-one hypotheses used by the
TeX-facing Step 3/4 lemmas.

This file is intentionally "plumbing-first":
it does not attempt to prove the rank-one fiber factorization from tube geometry.
Instead, it packages the minimal algebra needed to turn such a factorization into the
`innerSumUZ` / `innerSumVZ` hypotheses expected by
`TypeIIStep3RankOneApplyMVTeX` / `TypeIIStep4RankOneApplyMVTeX`.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII
open ZBoxRewrite

namespace RankOneFiberBridge

/-- Convert `zBoxN` into the corresponding endpoint formula, assuming the interval is nonempty
(`zBoxA ≤ zBoxB`). -/
theorem zBoxB_eq_zBoxA_add_zBoxN_of_le (td : TubeData) (hAB : zBoxA td ≤ zBoxB td) :
    zBoxA td + (zBoxN td : ℤ) = zBoxB td := by
  have hdiff : 0 ≤ zBoxB td - zBoxA td := sub_nonneg.mpr hAB
  have hN : (zBoxN td : ℤ) = zBoxB td - zBoxA td := by
    -- `Int.toNat_of_nonneg` gives the coercion identity.
    simpa [zBoxN, Int.toNat_of_nonneg hdiff]
  -- Finish by substitution.
  linarith [hN]

theorem zBoxB_eq_a_add_N_sub_one_of_le (td : TubeData) (hAB : zBoxA td ≤ zBoxB td) :
    (zBoxA td + 1) + (zBoxN td : ℤ) - 1 = zBoxB td := by
  have h := zBoxB_eq_zBoxA_add_zBoxN_of_le (td := td) hAB
  -- `(+1) - 1` cancels.
  linarith [h]

/-- Step 4 analogue of `zBoxB_eq_a_add_N_sub_one_of_le` for `zBoxV`. -/
theorem zBoxVB_eq_zBoxVA_add_zBoxVN_sub_one_of_le (td : TubeData) (hAB : zBoxVA td ≤ zBoxVB td) :
    zBoxVA td + (zBoxVN td : ℤ) - 1 = zBoxVB td := by
  have hdiff : 0 ≤ zBoxVB td + 1 - zBoxVA td := by linarith
  have hN : (zBoxVN td : ℤ) = zBoxVB td + 1 - zBoxVA td := by
    simpa [zBoxVN, Int.toNat_of_nonneg hdiff]
  -- Expand and cancel.
  linarith [hN]

end RankOneFiberBridge

namespace Step3RankOne

/-- If the fiber coefficient sums factor as `β u * α z` on the uniform `zBox` interval, then
`innerSumUZ` is rank-one in the sense required by the TeX-facing MV application lemma. -/
theorem innerSumUZ_eq_rankOne_of_fiberFactor_zBox
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (α β : ℤ → ℂ)
    (hAB : zBoxA td ≤ zBoxB td)
    (hCoeff :
      ∀ u : ℤ, u ∈ uSet td →
        ∀ z : ℤ, z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)) →
          (∑ p ∈ fiberUZ td u z, F p) = β u * α z) :
    ∀ u : ℤ, u ∈ uSet td →
      innerSumUZ td ξ F u
        =
      β u * (∑ z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)),
        α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ))) := by
  classical
  intro u hu
  -- Rewrite `innerSumUZ` over the explicit `Icc` and align the upper endpoint.
  have hsum :=
    innerSumUZ_eq_sum_Icc_zBox (td := td) (ξ := ξ) (F := F) (u := u)
  have hub :
      zBoxB td = (zBoxA td + 1) + (zBoxN td : ℤ) - 1 := by
    symm
    exact RankOneFiberBridge.zBoxB_eq_a_add_N_sub_one_of_le (td := td) hAB
  -- Replace the coefficient sums using `hCoeff`, then factor out `β u`.
  -- (We also rewrite `/ td.X` into `ξ/td.X` for compatibility with later lemmas.)
  calc
    innerSumUZ td ξ F u
        =
      ∑ z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)),
        (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
          simpa [hub] using hsum
    _ =
      ∑ z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)),
        (β u * α z) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          simp [hCoeff u hu z hz]
    _ =
      β u * (∑ z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)),
        α z * e (ξ * (u : ℝ) * (z : ℝ) / td.X)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ =
      β u * (∑ z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)),
        α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ))) := by
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Convenience wrapper: apply the TeX-facing MV lemma under a fiber-factorization hypothesis
on the uniform `zBox` interval. -/
theorem norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBox
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (α β : ℤ → ℂ)
    (R : ℕ)
    (hDist : ∀ i ∈ uSet td, ∀ j ∈ uSet td, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / td.X)| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / td.X ≠ 0)
    (hAB : zBoxA td ≤ zBoxB td)
    (hCoeff :
      ∀ u : ℤ, u ∈ uSet td →
        ∀ z : ℤ, z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)) →
          (∑ p ∈ fiberUZ td u z, F p) = β u * α z) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (∑ u ∈ uSet td, ‖β u‖ ^ 2) *
      ((zBoxN td : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log R)) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖α ((zBoxA td + 1) + (k : ℕ))‖ ^ 2) := by
  classical
  -- Build the `innerSumUZ` rank-one hypothesis from the fiber factorization.
  have hRankOne :
      ∀ u : ℤ, u ∈ uSet td →
        innerSumUZ td ξ F u
          =
        β u * (∑ z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)),
          α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ))) :=
    innerSumUZ_eq_rankOne_of_fiberFactor_zBox
      (td := td) (ξ := ξ) (F := F) (α := α) (β := β) (hAB := hAB) (hCoeff := hCoeff)
  -- Apply the existing MV wrapper.
  simpa using
    (Step3RankOne.norm_typeIISum_sq_le_one_add_log_of_rankOne_innerSumUZ
      (td := td) (ξ := ξ) (F := F)
      (a := (zBoxA td + 1)) (N := zBoxN td) (α := α) (β := β)
      (R := R) (hDist := hDist) (ht := ht) (ht0 := ht0) (hRankOne := hRankOne))

/-- Geometry-specialized variant of
`norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBox`, removing the explicit
distance-bound hypothesis on `uSet td`. -/
theorem norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBox_geom
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (α β : ℤ → ℂ)
    (hU0 : 0 ≤ td.U)
    (ht :
      |(ξ / td.X)| * (2 * Int.toNat (Int.ceil td.U) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / td.X ≠ 0)
    (hAB : zBoxA td ≤ zBoxB td)
    (hCoeff :
      ∀ u : ℤ, u ∈ uSet td →
        ∀ z : ℤ, z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)) →
          (∑ p ∈ fiberUZ td u z, F p) = β u * α z) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (∑ u ∈ uSet td, ‖β u‖ ^ 2) *
      ((zBoxN td : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U)))) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖α ((zBoxA td + 1) + (k : ℕ))‖ ^ 2) := by
  classical
  have hRankOne :
      ∀ u : ℤ, u ∈ uSet td →
        innerSumUZ td ξ F u
          =
        β u * (∑ z ∈ (Finset.Icc (zBoxA td + 1) ((zBoxA td + 1) + (zBoxN td : ℤ) - 1)),
          α z * e ((ξ / td.X) * (u : ℝ) * (z : ℝ))) :=
    innerSumUZ_eq_rankOne_of_fiberFactor_zBox
      (td := td) (ξ := ξ) (F := F) (α := α) (β := β) (hAB := hAB) (hCoeff := hCoeff)
  simpa using
    (Step3RankOne.norm_typeIISum_sq_le_one_add_log_of_rankOne_innerSumUZ_geom
      (td := td) (ξ := ξ) (F := F)
      (a := (zBoxA td + 1)) (N := zBoxN td) (α := α) (β := β)
      (hU0 := hU0) (ht := ht) (ht0 := ht0) (hRankOne := hRankOne))

end Step3RankOne

namespace Step4RankOne

/-- Step 4 analogue of `Step3RankOne.innerSumUZ_eq_rankOne_of_fiberFactor_zBox`. -/
theorem innerSumVZ_eq_rankOne_of_fiberFactor_zBoxV
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (α β : ℤ → ℂ)
    (hAB : zBoxVA td ≤ zBoxVB td)
    (hCoeff :
      ∀ v : ℤ, v ∈ vSet td →
        ∀ z : ℤ, z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)) →
          (∑ p ∈ fiberVZ td v z, F p) = β v * α z) :
    ∀ v : ℤ, v ∈ vSet td →
      innerSumVZ td ξ F v
        =
      β v * (∑ z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)),
        α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ))) := by
  classical
  intro v hv
  have hsum :=
    innerSumVZ_eq_sum_Icc_zBoxV (td := td) (ξ := ξ) (F := F) (v := v)
  have hub :
      zBoxVB td = zBoxVA td + (zBoxVN td : ℤ) - 1 := by
    symm
    exact RankOneFiberBridge.zBoxVB_eq_zBoxVA_add_zBoxVN_sub_one_of_le (td := td) hAB
  calc
    innerSumVZ td ξ F v
        =
      ∑ z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)),
        (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
          simpa [hub] using hsum
    _ =
      ∑ z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)),
        (β v * α z) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          simp [hCoeff v hv z hz]
    _ =
      β v * (∑ z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)),
        α z * e (ξ * (z : ℝ) * (v : ℝ) / td.X)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ =
      β v * (∑ z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)),
        α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ))) := by
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Step 4 analogue of `Step3RankOne.norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBox`. -/
theorem norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBoxV
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (α β : ℤ → ℂ)
    (R : ℕ)
    (hDist : ∀ i ∈ vSet td, ∀ j ∈ vSet td, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / td.X)| * (R : ℝ) ≤ (1 / 2 : ℝ)) (ht0 : ξ / td.X ≠ 0)
    (hAB : zBoxVA td ≤ zBoxVB td)
    (hCoeff :
      ∀ v : ℤ, v ∈ vSet td →
        ∀ z : ℤ, z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)) →
          (∑ p ∈ fiberVZ td v z, F p) = β v * α z) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (∑ v ∈ vSet td, ‖β v‖ ^ 2) *
      ((zBoxVN td : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log R)) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖α (zBoxVA td + (k : ℕ))‖ ^ 2) := by
  classical
  have hRankOne :
      ∀ v : ℤ, v ∈ vSet td →
        innerSumVZ td ξ F v
          =
        β v * (∑ z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)),
          α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ))) :=
    innerSumVZ_eq_rankOne_of_fiberFactor_zBoxV
      (td := td) (ξ := ξ) (F := F) (α := α) (β := β) (hAB := hAB) (hCoeff := hCoeff)
  simpa using
    (Step4RankOne.norm_typeIISum_sq_le_one_add_log_of_rankOne_innerSumVZ
      (td := td) (ξ := ξ) (F := F)
      (a := zBoxVA td) (N := zBoxVN td) (α := α) (β := β)
      (R := R) (hDist := hDist) (ht := ht) (ht0 := ht0) (hRankOne := hRankOne))

/-- Geometry-specialized variant of
`norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBoxV`, removing the explicit
distance-bound hypothesis on `vSet td`. -/
theorem norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBoxV_geom
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ)
    (α β : ℤ → ℂ)
    (hD0 : 0 ≤ td.D)
    (ht :
      |(ξ / td.X)| * (2 * Int.toNat (Int.ceil (2 * td.D)) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / td.X ≠ 0)
    (hAB : zBoxVA td ≤ zBoxVB td)
    (hCoeff :
      ∀ v : ℤ, v ∈ vSet td →
        ∀ z : ℤ, z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)) →
          (∑ p ∈ fiberVZ td v z, F p) = β v * α z) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (∑ v ∈ vSet td, ‖β v‖ ^ 2) *
      ((zBoxVN td : ℝ) + (1 / |(ξ / td.X)|) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D))))) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖α (zBoxVA td + (k : ℕ))‖ ^ 2) := by
  classical
  have hRankOne :
      ∀ v : ℤ, v ∈ vSet td →
        innerSumVZ td ξ F v
          =
        β v * (∑ z ∈ (Finset.Icc (zBoxVA td) (zBoxVA td + (zBoxVN td : ℤ) - 1)),
          α z * e ((ξ / td.X) * (v : ℝ) * (z : ℝ))) :=
    innerSumVZ_eq_rankOne_of_fiberFactor_zBoxV
      (td := td) (ξ := ξ) (F := F) (α := α) (β := β) (hAB := hAB) (hCoeff := hCoeff)
  simpa using
    (Step4RankOne.norm_typeIISum_sq_le_one_add_log_of_rankOne_innerSumVZ_geom
      (td := td) (ξ := ξ) (F := F)
      (a := zBoxVA td) (N := zBoxVN td) (α := α) (β := β)
      (hD0 := hD0) (ht := ht) (ht0 := ht0) (hRankOne := hRankOne))

end Step4RankOne

end

end LargeSieve
end TypeII
end Engines
end SSU
