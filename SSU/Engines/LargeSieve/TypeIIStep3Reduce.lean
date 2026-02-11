import SSU.Engines.LargeSieve.FinsetCS
import SSU.Engines.LargeSieve.TypeIISumDecompose
import SSU.Engines.LargeSieve.TypeIIResiduePartition
import SSU.Engines.TypeIILargeSieveTeX

/-!
Deterministic reduction of TeX Step 3 (LS-outer-u) to a single “fiber large sieve” hypothesis.

This file does *not* prove the Montgomery–Vaughan large sieve. Instead it:

1. rewrites `typeIISum` into the `(u,z)`-fiber form using `typeIISum_eq_sum_u_sum_z`;
2. applies a finite Cauchy–Schwarz inequality in the outer `u`-sum to reduce `‖S(ξ)‖²` to a sum
   of squared norms of the inner exponential sums in `z`.

What remains is an analytic inequality controlling that sum-of-squares by `tubeEnergy`.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

namespace LargeSieve

/-- The “inner” exponential sum on the `u`-fiber, after grouping by `z`. -/
def innerSumUZ (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (u : ℤ) : ℂ :=
  ∑ z ∈ zSet td u,
    (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X)

/-- TeX Step 3: on a fixed residue class `uClass td r`, rewrite the phase using
`u = u₀(r) + uIndex(r,u)*q`. This is purely algebraic bookkeeping for the later MV step. -/
theorem innerSumUZ_eq_phaseSplit_on_uClass
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (r u : ℤ)
    (hu : u ∈ ResiduePartition.uClass td r) :
    innerSumUZ td ξ F u
      =
    ∑ z ∈ zSet td u,
      (∑ p ∈ fiberUZ td u z, F p) *
        e (ξ * (uResidue td r : ℝ) * (z : ℝ) / td.X) *
        e (ξ * ((ResiduePartition.uIndex td r u : ℝ) * (td.q : ℝ)) * (z : ℝ) / td.X) := by
  classical
  -- Expand `innerSumUZ` and rewrite the `e`-phase pointwise.
  unfold innerSumUZ
  refine Finset.sum_congr rfl ?_
  intro z hz
  have hphase :=
    (ResiduePartition.e_mul_u_mul_z_div_X_eq_mul (td := td) (ξ := ξ) (u := u) (r := r) (z := z)
      (hu := hu))
  -- Multiply the phase identity by the fixed coefficient sum and reassociate.
  simpa [mul_assoc] using
    congrArg (fun t : ℂ => (∑ p ∈ fiberUZ td u z, F p) * t) hphase

/-- TeX Step 3 phase split, specialized to `u = uFromIndex r m` with `m ∈ uIndexSet r`.

This removes `uIndex` from the RHS entirely, which is the form needed for an MV-on-a-progression
application. -/
theorem innerSumUZ_uFromIndex_eq_phaseSplit
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (r m : ℤ)
    (hm : m ∈ ResiduePartition.uIndexSet (td := td) r) :
    innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)
      =
    ∑ z ∈ zSet td (ResiduePartition.uFromIndex (td := td) r m),
      (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m) z, F p) *
        e (ξ * (uResidue td r : ℝ) * (z : ℝ) / td.X) *
        e (ξ * ((m : ℝ) * (td.q : ℝ)) * (z : ℝ) / td.X) := by
  classical
  have hu :
      ResiduePartition.uFromIndex (td := td) r m ∈ ResiduePartition.uClass td r :=
    ResiduePartition.uFromIndex_mem_uClass_of_mem_uIndexSet (td := td) (r := r) (m := m) hm
  -- Start from the general phase-split lemma, then rewrite `uIndex (uFromIndex m) = m`.
  have hsplit :=
    innerSumUZ_eq_phaseSplit_on_uClass (td := td) (ξ := ξ) (F := F) (r := r)
      (u := ResiduePartition.uFromIndex (td := td) r m) hu
  have huIndex :
      ResiduePartition.uIndex td r (ResiduePartition.uFromIndex (td := td) r m) = m :=
    ResiduePartition.uIndex_uFromIndex_of_mem_uIndexSet (td := td) (r := r) (m := m) hm
  simpa [huIndex] using hsplit

/-- Bookkeeping rewrite: partition the Step 3 sum over `u` into residue classes
`vResidue td u ∈ [0,q)`. -/
theorem sum_uSet_norm_innerSumUZ_sq_eq_sum_residueClasses
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
      =
    ∑ r ∈ ResiduePartition.residuesU td,
      ∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2 := by
  classical
  -- Directly apply the deterministic partition lemma.
  simpa using
    (ResiduePartition.sum_uSet_eq_sum_residueClasses (td := td)
      (f := fun u : ℤ => ‖innerSumUZ td ξ F u‖ ^ 2))

/-- Reindex a fixed residue class `uClass td r` by the progression parameter `uIndex`.

This is purely deterministic bookkeeping for the later MV-on-a-progression step. -/
theorem sum_uClass_norm_innerSumUZ_sq_eq_sum_uIndexSet
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (r : ℤ) :
    (ResiduePartition.uClass td r).sum (fun u => ‖innerSumUZ td ξ F u‖ ^ 2)
      =
    (ResiduePartition.uIndexSet (td := td) r).sum
      (fun m => ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2) := by
  classical
  simpa using
    (ResiduePartition.sum_uClass_eq_sum_uIndexSet (td := td) (r := r)
      (f := fun u : ℤ => ‖innerSumUZ td ξ F u‖ ^ 2))

/-- Combine the residue-class partition with reindexing by the progression parameter `uIndex`. -/
theorem sum_uSet_norm_innerSumUZ_sq_eq_sum_residueClasses_uIndexSet
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
      =
    ∑ r ∈ ResiduePartition.residuesU td,
      ∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2 := by
  classical
  -- First split `uSet` into the residue classes, then reindex each class by `uIndex`.
  calc
    (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
        =
      ∑ r ∈ ResiduePartition.residuesU td,
        ∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2 := by
          simpa using sum_uSet_norm_innerSumUZ_sq_eq_sum_residueClasses (td := td) (ξ := ξ) (F := F)
    _ =
      ∑ r ∈ ResiduePartition.residuesU td,
        ∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
          ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          -- Apply the class-by-class reindexing lemma.
          simpa using
            (sum_uClass_norm_innerSumUZ_sq_eq_sum_uIndexSet (td := td) (ξ := ξ) (F := F) (r := r))

/-- TeX Step 3 in a form that matches the analytic large sieve directly: a sum of squared norms of
`innerSumUZ` over `u`. -/
structure Step3FiberLargeSieve (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
          ≤
        C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F)

theorem typeIISum_eq_outer_u_innerUZ (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    typeIISum td.a td.q td.X ξ td.T F
      =
    ∑ u ∈ uSet td,
      (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) * innerSumUZ td ξ F u := by
  classical
  -- Expand to the `(u,z)` double sum, then package the inner `z`-sum as `innerSumUZ`.
  simpa [innerSumUZ, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
    (typeIISum_eq_sum_u_sum_z (td := td) (ξ := ξ) (F := F))

def step3OuterU_of_fiberLargeSieve (td : TubeData) (hLS : Step3FiberLargeSieve td) :
    Step3LargeSieveOuterU td :=
by
  classical
  refine ⟨hLS.C * (uSet td).card, ?_, ?_⟩
  · exact mul_nonneg hLS.C_nonneg (by positivity)
  intro ξ hξ0 hξH F
  -- Rewrite `typeIISum` as an outer `u`-sum of `innerSumUZ`.
  have hdecomp := typeIISum_eq_outer_u_innerUZ (td := td) (ξ := ξ) (F := F)
  -- Drop the unimodular phase `e(...)` in the norm, and apply finite Cauchy–Schwarz in `u`.
  have hcs :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      ((uSet td).card : ℝ) * ∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2 := by
    -- Convert to the bound on `‖∑ (phase * inner)‖²`.
    -- Use `‖phase * x‖ = ‖x‖` since `‖phase‖ = 1`.
    have hcs' :
        ‖∑ u ∈ uSet td,
            (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) * innerSumUZ td ξ F u‖ ^ 2
          ≤
        ((uSet td).card : ℝ) *
          ∑ u ∈ uSet td,
            ‖(e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) * innerSumUZ td ξ F u‖ ^ 2 := by
      simpa using
        (norm_sum_sq_le_card_mul_sum_norm_sq (s := uSet td)
          (f := fun u =>
            (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) * innerSumUZ td ξ F u))
    have hsimp :
        ∑ u ∈ uSet td,
            (‖e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))‖ *
                ‖innerSumUZ td ξ F u‖) ^ 2
          =
        ∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro u hu
      simp [norm_e]
    -- Substitute the decomposition and finish.
    simpa [hdecomp, hsimp] using hcs'
  -- Convert the `Nat` factor to `ℝ` and apply the analytic hypothesis `hLS`.
  -- (`n : ℕ` coerces to `ℝ` in the final inequality.)
  have hLS' := hLS.bound ξ hξ0 hξH F
  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤ ((uSet td).card : ℝ) * ∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2 := hcs
    _ ≤ ((uSet td).card : ℝ) *
          (hLS.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F)) := by
          exact mul_le_mul_of_nonneg_left hLS' (by positivity)
    _ = (hLS.C * (uSet td).card) * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F) := by
          ring

end LargeSieve

end
end TypeII
end Engines
end SSU
