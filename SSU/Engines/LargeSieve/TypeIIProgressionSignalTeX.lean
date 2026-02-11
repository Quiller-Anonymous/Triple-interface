import SSU.Engines.LargeSieve.TypeIIRankOneShearCoeffs
import SSU.Engines.LargeSieve.TypeIIStep3Reduce
import SSU.Engines.LargeSieve.TypeIIStep4Reduce
import SSU.Engines.LargeSieve.TypeIIShearSumTeX

/-!
TeX Step 3/4 “progressions” rewrites for the Type–II oscillatory sum.

This file records purely deterministic identities that match the displayed expansions in
`SupportingDocs/Goldbach tenor/sections/05b_SSU.tex`, lines 535–557:

* Step 3: for each `u`, write `v = vResidue(u) + z*q` (a progression in `v`);
* Step 4: for each `v`, write `u = uResidue(v) + z*q` (a progression in `u`).

We package these as lemmas for the rank-one shear coefficient model
`F(d,n) = α(v) * β(u)` with `u := shearU a q (d,n)` and `v := shearV (d,n)`.

No analytic bounds happen here.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

namespace RankOneShear

/-- TeX Step 3 expansion of `S(ξ)` (our `typeIISum`) for rank-one shear coefficients:
outer sum over `u`, inner sum over the progression parameter `z` (so `v = v₀(u) + z*q`). -/
theorem typeIISum_eq_outer_u_rankOne_progression
    (td : TubeData) (ξ : ℝ) (α β : ℤ → ℂ) :
    typeIISum td.a td.q td.X ξ td.T (coeff td α β)
      =
    ∑ u ∈ uSet td,
      (β u * e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
        (∑ z ∈ zSet td u,
          α (vResidue td u + z * td.q) * e (ξ * (u : ℝ) * (z : ℝ) / td.X)) := by
  classical
  -- Start from the deterministic outer-`u` decomposition.
  have hdecomp := typeIISum_eq_outer_u_innerUZ (td := td) (ξ := ξ) (F := coeff td α β)
  -- Substitute the rank-one inner sum.
  have hinner := innerSumUZ_eq_rankOne (td := td) (ξ := ξ) (α := α) (β := β)
  -- Rewrite and reassociate scalar factors.
  rw [hdecomp]
  refine Finset.sum_congr rfl ?_
  intro u hu
  -- `simp` performs the substitution and commutes the scalar factors.
  simpa [hinner, mul_assoc, mul_left_comm, mul_comm]

/-- TeX Step 4 expansion of `S(ξ)` (our `typeIISum`) for rank-one shear coefficients:
outer sum over `v`, inner sum over the progression parameter `z` (so `u = u₀(v) + z*q`). -/
theorem typeIISum_eq_outer_v_rankOne_progression
    (td : TubeData) (ξ : ℝ) (α β : ℤ → ℂ) :
    typeIISum td.a td.q td.X ξ td.T (coeff td α β)
      =
    ∑ v ∈ vSet td,
      (α v * e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
        (∑ z ∈ zSetV td v,
          β (uResidue td v + z * td.q) * e (ξ * (z : ℝ) * (v : ℝ) / td.X)) := by
  classical
  have hdecomp := typeIISum_eq_outer_v_innerVZ (td := td) (ξ := ξ) (F := coeff td α β)
  have hinner := innerSumVZ_eq_rankOne (td := td) (ξ := ξ) (α := α) (β := β)
  rw [hdecomp]
  refine Finset.sum_congr rfl ?_
  intro v hv
  simpa [hinner, mul_assoc, mul_left_comm, mul_comm]

/-!
### Optional: residue-class specializations (matching TeX’s “fix the congruence class” step)

On a fixed residue class, the residue representative becomes literally constant.
These lemmas are just repackagings of the previous two using
`innerSumUZ_eq_rankOne_on_uClass` / `innerSumVZ_eq_rankOne_on_vClass`.
-/

theorem typeIISum_eq_sum_uClass_rankOne_progression
    (td : TubeData) (ξ : ℝ) (α β : ℤ → ℂ) (r : ℤ) :
    (∑ u ∈ ResiduePartition.uClass td r,
        (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) *
          innerSumUZ td ξ (coeff td α β) u)
      =
    ∑ u ∈ ResiduePartition.uClass td r,
      (β u * e (ξ * (u : ℝ) * (r : ℝ) / ((td.q : ℝ) * td.X))) *
        (∑ z ∈ zSet td u,
          α (r + z * td.q) * e (ξ * (u : ℝ) * (z : ℝ) / td.X)) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro u hu
  have hr : vResidue td u = r := by
    simpa [ResiduePartition.uClass] using (Finset.mem_filter.1 hu).2
  -- Apply the rank-one-on-class inner sum rewrite.
  have hinner :=
    innerSumUZ_eq_rankOne_on_uClass (td := td) (ξ := ξ) (α := α) (β := β) (r := r) (u := u) hu
  -- Substitute and simplify the phase.
  simp [hr, hinner, mul_assoc, mul_left_comm, mul_comm]

theorem typeIISum_eq_sum_vClass_rankOne_progression
    (td : TubeData) (ξ : ℝ) (α β : ℤ → ℂ) (r : ℤ) :
    (∑ v ∈ ResiduePartitionV.vClass td r,
        (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
          innerSumVZ td ξ (coeff td α β) v)
      =
    ∑ v ∈ ResiduePartitionV.vClass td r,
      (α v * e (ξ * (r : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) *
        (∑ z ∈ zSetV td v,
          β (r + z * td.q) * e (ξ * (z : ℝ) * (v : ℝ) / td.X)) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro v hv
  have hr : uResidue td v = r := by
    simpa [ResiduePartitionV.vClass] using (Finset.mem_filter.1 hv).2
  have hinner :=
    innerSumVZ_eq_rankOne_on_vClass (td := td) (ξ := ξ) (α := α) (β := β) (r := r) (v := v) hv
  simp [hr, hinner, mul_assoc, mul_left_comm, mul_comm]

/-- TeX-facing rewrite: if `F` factors through the shear map, we can sum directly over the shear image.

This matches the TeX definition `S(ξ) = ∑_{(u,v)∈T'} F(u,v) e(ξ u v /(qX))` once `T'` is taken
to be the shear image of `td.T`. -/
theorem typeIISum_eq_shearSum_image_rankOneShear
    (td : TubeData) (ξ : ℝ) (α β : ℤ → ℂ) :
    typeIISum td.a td.q td.X ξ td.T (coeff td α β)
      =
    shearSum td.q td.X ξ (td.T.image (shearMap td.a td.q)) (fun uv => α uv.2 * β uv.1) := by
  -- Use the general “factors through shearMap” lemma.
  simpa [RankOneShear.coeff, coeff] using
    (typeIISum_eq_shearSum_image_of_comp (td := td) (ξ := ξ)
      (G := fun uv : ShearPoint => α uv.2 * β uv.1))

theorem tubeEnergy_eq_sum_image_shearMap_rankOneShear
    (td : TubeData) (α β : ℤ → ℂ) :
    tubeEnergy td.T (coeff td α β)
      =
    ∑ uv ∈ td.T.image (shearMap td.a td.q), ‖α uv.2 * β uv.1‖ ^ 2 := by
  simpa [RankOneShear.coeff, coeff] using
    (tubeEnergy_eq_sum_image_shearMap_of_comp (td := td)
      (G := fun uv : ShearPoint => α uv.2 * β uv.1))

end RankOneShear

end

end LargeSieve
end TypeII
end Engines
end SSU
