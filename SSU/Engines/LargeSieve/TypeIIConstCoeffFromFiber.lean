import SSU.Engines.LargeSieve.TypeIIZBoxToFin
import SSU.Engines.LargeSieve.TypeIIResiduePartition

/-!
Deterministic helpers for proving the Type–II Step 3/4 *const-coefficient* hypotheses.

These lemmas are intentionally simple:
they reduce constancy of the `Fin`-indexed coefficient arrays `coeffUZFin` / `coeffVZFin`
to constancy of the underlying fiber sums
`∑ p ∈ fiberUZ td u z, F p` / `∑ p ∈ fiberVZ td v z, F p`.

They are meant to be used in the “first real hypothesis → proof” stage, where tube geometry (or a
rank-one box model) gives a canonical identification of fibers across different outer indices.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open ZBoxRewrite
open ZBoxToFin

namespace ConstCoeffFromFiber

/-- If all Step 3 fibers have the same coefficient sums as a fixed reference `u₀`, then the `Fin`-indexed
coefficient array `coeffUZFin` is constant on `uSet`. -/
theorem exists_constCoeffUZFin_of_sum_fiberUZ_eq_ref
    (td : TubeData) (F : TubePoint → ℂ)
    (u0 : ℤ) (_hu0 : u0 ∈ uSet td)
    (hEq :
      ∀ u : ℤ, u ∈ uSet td →
        ∀ k : Fin (zBoxN td),
          (∑ p ∈ fiberUZ td u (zBoxA td + 1 + (k : ℕ)), F p)
            =
          (∑ p ∈ fiberUZ td u0 (zBoxA td + 1 + (k : ℕ)), F p)) :
    ∃ a : Fin (zBoxN td) → ℂ, ∀ u : ℤ, u ∈ uSet td → coeffUZFin td F u = a := by
  classical
  refine ⟨coeffUZFin td F u0, ?_⟩
  intro u hu
  funext k
  -- Unfold `coeffUZFin`, then rewrite the fiber sum using the hypothesis.
  simpa [coeffUZFin] using (hEq u hu k)

/-- Step 4 analogue of `exists_constCoeffUZFin_of_sum_fiberUZ_eq_ref`. -/
theorem exists_constCoeffVZFin_of_sum_fiberVZ_eq_ref
    (td : TubeData) (F : TubePoint → ℂ)
    (v0 : ℤ) (_hv0 : v0 ∈ vSet td)
    (hEq :
      ∀ v : ℤ, v ∈ vSet td →
        ∀ k : Fin (zBoxVN td),
          (∑ p ∈ fiberVZ td v (zBoxVA td + (k : ℕ)), F p)
            =
          (∑ p ∈ fiberVZ td v0 (zBoxVA td + (k : ℕ)), F p)) :
    ∃ a : Fin (zBoxVN td) → ℂ, ∀ v : ℤ, v ∈ vSet td → coeffVZFin td F v = a := by
  classical
  refine ⟨coeffVZFin td F v0, ?_⟩
  intro v hv
  funext k
  simpa [coeffVZFin] using (hEq v hv k)

/-- Residue-class Step 3 variant of `exists_constCoeffUZFin_of_sum_fiberUZ_eq_ref`.

If all Step 3 fibers along a fixed progression `u = u₀(r) + m*q` have the same coefficient sums
as a fixed reference index `m₀`, then `coeffUZFin td F (uFromIndex r m)` is constant on the
progression-index set `uIndexSet td r`.

This matches the coefficient-constancy hypothesis required by
`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_finiteLargeSieve`. -/
theorem exists_constCoeffUZFin_of_sum_fiberUZ_uFromIndex_eq_ref
    (td : TubeData) (F : TubePoint → ℂ) (r : ℤ)
    (m0 : ℤ) (_hm0 : m0 ∈ ResiduePartition.uIndexSet (td := td) r)
    (hEq :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        ∀ k : Fin (zBoxN td),
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m)
              (zBoxA td + 1 + (k : ℕ)), F p)
            =
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0)
              (zBoxA td + 1 + (k : ℕ)), F p)) :
    ∃ a : Fin (zBoxN td) → ℂ,
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m) = a := by
  classical
  refine ⟨coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m0), ?_⟩
  intro m hm
  funext k
  simpa [coeffUZFin] using (hEq m hm k)

/-- Step 3 residue-class constancy from equality only on the reference `zSet`.

This is a refinement of `exists_constCoeffUZFin_of_sum_fiberUZ_uFromIndex_eq_ref`: instead of
assuming equality for every translated `z`-index in `zBox`, it is enough to assume:
1. all `zSet` domains along the progression equal the reference domain, and
2. fiber-sum equality on that common domain.

Outside the common domain, both sides are `0` by support.
-/
theorem constCoeffUZFin_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet
    (td : TubeData) (F : TubePoint → ℂ) (r : ℤ)
    (m0 : ℤ) (_hm0 : m0 ∈ ResiduePartition.uIndexSet (td := td) r)
    (hZeq :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        zSet td (ResiduePartition.uFromIndex (td := td) r m)
          = zSet td (ResiduePartition.uFromIndex (td := td) r m0))
    (hEqOn :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        ∀ z : ℤ, z ∈ zSet td (ResiduePartition.uFromIndex (td := td) r m0) →
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m) z, F p)
            =
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0) z, F p)) :
    ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
      coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m)
        =
      coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m0) := by
  classical
  intro m hm
  funext k
  let z : ℤ := zBoxA td + 1 + (k : ℕ)
  by_cases hz0 : z ∈ zSet td (ResiduePartition.uFromIndex (td := td) r m0)
  · simpa [coeffUZFin, z] using (hEqOn m hm z hz0)
  · have hzEq : zSet td (ResiduePartition.uFromIndex (td := td) r m)
        = zSet td (ResiduePartition.uFromIndex (td := td) r m0) := hZeq m hm
    have hzm : z ∉ zSet td (ResiduePartition.uFromIndex (td := td) r m) := by
      intro hzM
      exact hz0 (by simpa [hzEq] using hzM)
    have hL :
        (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m) z, F p) = 0 :=
      sum_fiberUZ_eq_zero_of_not_mem_zSet (td := td) (F := F)
        (u := ResiduePartition.uFromIndex (td := td) r m) (z := z) hzm
    have hR :
        (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0) z, F p) = 0 :=
      sum_fiberUZ_eq_zero_of_not_mem_zSet (td := td) (F := F)
        (u := ResiduePartition.uFromIndex (td := td) r m0) (z := z) hz0
    simpa [coeffUZFin, z, hL, hR]

/-- Residue-class Step 4 variant of `exists_constCoeffVZFin_of_sum_fiberVZ_eq_ref`.

If all Step 4 fibers along a fixed progression `v = v₀(r) + m*q` have the same coefficient sums
as a fixed reference index `m₀`, then `coeffVZFin td F (vFromIndex r m)` is constant on the
progression-index set `vIndexSet td r`. -/
theorem exists_constCoeffVZFin_of_sum_fiberVZ_vFromIndex_eq_ref
    (td : TubeData) (F : TubePoint → ℂ) (r : ℤ)
    (m0 : ℤ) (_hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := td) r)
    (hEq :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        ∀ k : Fin (zBoxVN td),
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m)
              (zBoxVA td + (k : ℕ)), F p)
            =
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0)
              (zBoxVA td + (k : ℕ)), F p)) :
    ∃ a : Fin (zBoxVN td) → ℂ,
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m) = a := by
  classical
  refine ⟨coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m0), ?_⟩
  intro m hm
  funext k
  simpa [coeffVZFin] using (hEq m hm k)

/-- Step 4 analogue of `constCoeffUZFin_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet`. -/
theorem constCoeffVZFin_of_sum_fiberVZ_vFromIndex_eq_ref_on_zSetV
    (td : TubeData) (F : TubePoint → ℂ) (r : ℤ)
    (m0 : ℤ) (_hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := td) r)
    (hZeq :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        zSetV td (ResiduePartitionV.vFromIndex (td := td) r m)
          = zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0))
    (hEqOn :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        ∀ z : ℤ, z ∈ zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0) →
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m) z, F p)
            =
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0) z, F p)) :
    ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
      coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m)
        =
      coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m0) := by
  classical
  intro m hm
  funext k
  let z : ℤ := zBoxVA td + (k : ℕ)
  by_cases hz0 : z ∈ zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0)
  · simpa [coeffVZFin, z] using (hEqOn m hm z hz0)
  · have hzEq : zSetV td (ResiduePartitionV.vFromIndex (td := td) r m)
        = zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0) := hZeq m hm
    have hzm : z ∉ zSetV td (ResiduePartitionV.vFromIndex (td := td) r m) := by
      intro hzM
      exact hz0 (by simpa [hzEq] using hzM)
    have hL :
        (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m) z, F p) = 0 :=
      sum_fiberVZ_eq_zero_of_not_mem_zSetV (td := td) (F := F)
        (v := ResiduePartitionV.vFromIndex (td := td) r m) (z := z) hzm
    have hR :
        (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0) z, F p) = 0 :=
      sum_fiberVZ_eq_zero_of_not_mem_zSetV (td := td) (F := F)
        (v := ResiduePartitionV.vFromIndex (td := td) r m0) (z := z) hz0
    simpa [coeffVZFin, z, hL, hR]

end ConstCoeffFromFiber

end

end LargeSieve
end TypeII
end Engines
end SSU
