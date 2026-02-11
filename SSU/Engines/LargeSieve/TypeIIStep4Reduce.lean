import SSU.Engines.LargeSieve.FinsetCS
import SSU.Engines.LargeSieve.TypeIISumDecomposeV
import SSU.Engines.LargeSieve.TypeIIResiduePartition
import SSU.Engines.TypeIILargeSieveTeX

/-!
Deterministic reduction of TeX Step 4 (LS-outer-v) to a single “fiber large sieve” hypothesis.

This is the `v`-analogue of `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean`.

We do *not* prove the Montgomery–Vaughan large sieve here. We only:

1. rewrite `typeIISum` into the `(v,z)`-fiber form using `typeIISum_eq_sum_v_sum_z`;
2. apply finite Cauchy–Schwarz in the outer `v`-sum to reduce `‖S(ξ)‖²` to a sum of squared norms
   of inner exponential sums indexed by `z`.

What remains is an analytic inequality controlling that sum-of-squares by `tubeEnergy`.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

namespace LargeSieve

/-- The “inner” exponential sum on the `v`-fiber, after grouping by `z`. -/
def innerSumVZ (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (v : ℤ) : ℂ :=
  ∑ z ∈ zSetV td v,
    (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X)

/-- TeX Step 4: on a fixed residue class `vClass td r`, rewrite the phase using
`v = v₀(r) + vIndex(r,v)*q`. This is purely algebraic bookkeeping for the later MV step. -/
theorem innerSumVZ_eq_phaseSplit_on_vClass
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (r v : ℤ)
    (hv : v ∈ ResiduePartitionV.vClass td r) :
    innerSumVZ td ξ F v
      =
    ∑ z ∈ zSetV td v,
      (∑ p ∈ fiberVZ td v z, F p) *
        e (ξ * (z : ℝ) * (vResidue td r : ℝ) / td.X) *
        e (ξ * (z : ℝ) * ((ResiduePartitionV.vIndex td r v : ℝ) * (td.q : ℝ)) / td.X) := by
  classical
  unfold innerSumVZ
  refine Finset.sum_congr rfl ?_
  intro z hz
  have hphase :=
    (ResiduePartitionV.e_mul_z_mul_v_div_X_eq_mul (td := td) (ξ := ξ) (v := v) (r := r) (z := z)
      (hv := hv))
  simpa [mul_assoc] using
    congrArg (fun t : ℂ => (∑ p ∈ fiberVZ td v z, F p) * t) hphase

/-- TeX Step 4 phase split, specialized to `v = vFromIndex r m` with `m ∈ vIndexSet r`. -/
theorem innerSumVZ_vFromIndex_eq_phaseSplit
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (r m : ℤ)
    (hm : m ∈ ResiduePartitionV.vIndexSet (td := td) r) :
    innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)
      =
    ∑ z ∈ zSetV td (ResiduePartitionV.vFromIndex (td := td) r m),
      (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m) z, F p) *
        e (ξ * (z : ℝ) * (vResidue td r : ℝ) / td.X) *
        e (ξ * (z : ℝ) * ((m : ℝ) * (td.q : ℝ)) / td.X) := by
  classical
  have hv :
      ResiduePartitionV.vFromIndex (td := td) r m ∈ ResiduePartitionV.vClass td r :=
    ResiduePartitionV.vFromIndex_mem_vClass_of_mem_vIndexSet (td := td) (r := r) (m := m) hm
  have hsplit :=
    innerSumVZ_eq_phaseSplit_on_vClass (td := td) (ξ := ξ) (F := F) (r := r)
      (v := ResiduePartitionV.vFromIndex (td := td) r m) hv
  have hvIndex :
      ResiduePartitionV.vIndex td r (ResiduePartitionV.vFromIndex (td := td) r m) = m :=
    ResiduePartitionV.vIndex_vFromIndex_of_mem_vIndexSet (td := td) (r := r) (m := m) hm
  simpa [hvIndex] using hsplit

/-- Bookkeeping rewrite: partition the Step 4 sum over `v` into residue classes
`uResidue td v ∈ [0,q)`. -/
theorem sum_vSet_norm_innerSumVZ_sq_eq_sum_residueClasses
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
      =
    ∑ r ∈ ResiduePartitionV.residuesV td,
      ∑ v ∈ ResiduePartitionV.vClass td r, ‖innerSumVZ td ξ F v‖ ^ 2 := by
  classical
  simpa using
    (ResiduePartitionV.sum_vSet_eq_sum_residueClasses (td := td)
      (f := fun v : ℤ => ‖innerSumVZ td ξ F v‖ ^ 2))

/-- Reindex a fixed residue class `vClass td r` by the progression parameter `vIndex`.

This is purely deterministic bookkeeping for the later MV-on-a-progression step. -/
theorem sum_vClass_norm_innerSumVZ_sq_eq_sum_vIndexSet
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (r : ℤ) :
    (ResiduePartitionV.vClass td r).sum (fun v => ‖innerSumVZ td ξ F v‖ ^ 2)
      =
    (ResiduePartitionV.vIndexSet (td := td) r).sum
      (fun m => ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2) := by
  classical
  simpa using
    (ResiduePartitionV.sum_vClass_eq_sum_vIndexSet (td := td) (r := r)
      (f := fun v : ℤ => ‖innerSumVZ td ξ F v‖ ^ 2))

/-- Combine the residue-class partition with reindexing by the progression parameter `vIndex`. -/
theorem sum_vSet_norm_innerSumVZ_sq_eq_sum_residueClasses_vIndexSet
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
      =
    ∑ r ∈ ResiduePartitionV.residuesV td,
      ∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2 := by
  classical
  calc
    (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
        =
      ∑ r ∈ ResiduePartitionV.residuesV td,
        ∑ v ∈ ResiduePartitionV.vClass td r, ‖innerSumVZ td ξ F v‖ ^ 2 := by
          simpa using sum_vSet_norm_innerSumVZ_sq_eq_sum_residueClasses (td := td) (ξ := ξ) (F := F)
    _ =
      ∑ r ∈ ResiduePartitionV.residuesV td,
        ∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
          ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          simpa using
            (sum_vClass_norm_innerSumVZ_sq_eq_sum_vIndexSet (td := td) (ξ := ξ) (F := F) (r := r))

/-- TeX Step 4 in a form that matches the analytic large sieve directly: a sum of squared norms of
`innerSumVZ` over `v`. -/
structure Step4FiberLargeSieve (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
          ≤
        C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F)

theorem typeIISum_eq_outer_v_innerVZ (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) :
    typeIISum td.a td.q td.X ξ td.T F
      =
    ∑ v ∈ vSet td,
      (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) * innerSumVZ td ξ F v := by
  classical
  simpa [innerSumVZ, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
    (typeIISum_eq_sum_v_sum_z (td := td) (ξ := ξ) (F := F))

def step4OuterV_of_fiberLargeSieve (td : TubeData) (hLS : Step4FiberLargeSieve td) :
    Step4LargeSieveOuterV td :=
by
  classical
  refine ⟨hLS.C * (vSet td).card, ?_, ?_⟩
  · exact mul_nonneg hLS.C_nonneg (by positivity)
  intro ξ hξ0 hξH F
  have hdecomp := typeIISum_eq_outer_v_innerVZ (td := td) (ξ := ξ) (F := F)
  have hcs :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      ((vSet td).card : ℝ) * ∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2 := by
    have hcs' :
        ‖∑ v ∈ vSet td,
            (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) * innerSumVZ td ξ F v‖ ^ 2
          ≤
        ((vSet td).card : ℝ) *
          ∑ v ∈ vSet td,
            ‖(e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) * innerSumVZ td ξ F v‖ ^ 2 := by
      simpa using
        (norm_sum_sq_le_card_mul_sum_norm_sq (s := vSet td)
          (f := fun v =>
            (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) * innerSumVZ td ξ F v))
    have hsimp :
        ∑ v ∈ vSet td,
            (‖e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))‖ *
                ‖innerSumVZ td ξ F v‖) ^ 2
          =
        ∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simp [norm_e]
    -- `simp` rewrites `‖phase * x‖` as `‖phase‖ * ‖x‖`, so we rewrite to `hsimp`.
    simpa [hdecomp, norm_mul, hsimp] using hcs'
  have hLS' := hLS.bound ξ hξ0 hξH F
  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤ ((vSet td).card : ℝ) * ∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2 := hcs
    _ ≤ ((vSet td).card : ℝ) *
          (hLS.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F)) := by
          exact mul_le_mul_of_nonneg_left hLS' (by positivity)
    _ = (hLS.C * (vSet td).card) * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F) := by
          ring

end LargeSieve

end
end TypeII
end Engines
end SSU
