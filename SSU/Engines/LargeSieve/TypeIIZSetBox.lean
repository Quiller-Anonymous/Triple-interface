import SSU.Engines.LargeSieve.TypeIIZSetCard
import SSU.Engines.LargeSieve.TypeIIZSetVCard

/-!
Uniform “box” supersets for the progression index sets `zSet` and `zSetV`.

In TeX Step 3/4, for each fixed outer index (either `u` or `v`) the inner index `z` ranges over
an interval whose endpoints depend on the residue class `v₀(u)` or `u₀(v)` modulo `q`.

For applying a *single* finite large sieve inequality, it is convenient to enlarge these
`z`-intervals to a **uniform** interval independent of the outer index. This file provides that
deterministic containment.

Nothing analytic happens here.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace IndexBounds

open SSU.Engines.TypeII

/-!
## Step 3 (outer `u`): uniform `z`-box
-/

/-- A uniform interval containing every `zSet td u` (Step 3), ignoring dependence on `v₀(u)`.

We use a deliberately lax lower bound `D - q ≤ D - v₀(u)` and upper bound `2D - v₀(u) ≤ 2D`,
so the endpoints depend only on `D,q`. -/
def zBox (td : TubeData) : Finset ℤ :=
  Finset.Ioc
    (⌊(td.D - (td.q : ℝ)) / (td.q : ℝ)⌋ : ℤ)
    (⌈(2 * td.D) / (td.q : ℝ)⌉ : ℤ)

theorem mem_zSet_imp_mem_zBox (td : TubeData) {u z : ℤ} (hz : z ∈ zSet td u) :
    z ∈ zBox td := by
  classical
  have hq : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
  -- Start from the precise interval bound depending on `v₀(u)`.
  have hzI : z ∈
      (Finset.Ioc
        (⌊(td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌋ : ℤ)
        (⌈(2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌉ : ℤ)) :=
    mem_zSet_imp_mem_Ioc_floor_ceil (td := td) (u := u) (z := z) hz
  have hzI' : (⌊(td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌋ : ℤ) < z ∧
      z ≤ (⌈(2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌉ : ℤ) := by
    simpa [Finset.mem_Ioc] using hzI
  -- Compare left endpoints: `floor((D-q)/q) ≤ floor((D-v0)/q)`.
  have hv0_le_q : (vResidue td u : ℝ) ≤ (td.q : ℝ) := by
    have : (vResidue td u : ℝ) < (td.q : ℝ) := by
      exact_mod_cast (vResidue_lt td u)
    exact le_of_lt this
  have hleft_le :
      (⌊(td.D - (td.q : ℝ)) / (td.q : ℝ)⌋ : ℤ)
        ≤
      (⌊(td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌋ : ℤ) := by
    have hnum :
        (td.D - (td.q : ℝ)) ≤ (td.D - (vResidue td u : ℤ)) := by
      -- `-q ≤ -v0`.
      have : -(td.q : ℝ) ≤ -(vResidue td u : ℝ) := by
        exact neg_le_neg hv0_le_q
      linarith
    have hdiv :
        (td.D - (td.q : ℝ)) / (td.q : ℝ)
          ≤
        (td.D - (vResidue td u : ℤ)) / (td.q : ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hq)
    exact Int.floor_mono hdiv
  have hz_left : (⌊(td.D - (td.q : ℝ)) / (td.q : ℝ)⌋ : ℤ) < z := by
    exact lt_of_le_of_lt hleft_le hzI'.1
  -- Compare right endpoints: `ceil((2D - v0)/q) ≤ ceil(2D/q)`.
  have hv0_nonneg : (0 : ℝ) ≤ (vResidue td u : ℝ) := by
    exact_mod_cast (vResidue_nonneg td u)
  have hright_le :
      (⌈(2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌉ : ℤ)
        ≤
      (⌈(2 * td.D) / (td.q : ℝ)⌉ : ℤ) := by
    have hnum : (2 * td.D - (vResidue td u : ℤ)) ≤ (2 * td.D) := by
      -- subtracting a nonnegative term
      have : (0 : ℝ) ≤ (vResidue td u : ℝ) := hv0_nonneg
      linarith
    have hdiv :
        (2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ) ≤ (2 * td.D) / (td.q : ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hq)
    exact Int.ceil_mono hdiv
  have hz_right : z ≤ (⌈(2 * td.D) / (td.q : ℝ)⌉ : ℤ) := le_trans hzI'.2 hright_le
  -- Assemble membership in the uniform interval.
  simpa [zBox, Finset.mem_Ioc] using And.intro hz_left hz_right

theorem zSet_subset_zBox (td : TubeData) (u : ℤ) : zSet td u ⊆ zBox td := by
  intro z hz
  exact mem_zSet_imp_mem_zBox (td := td) (u := u) (z := z) hz

/-!
## Step 4 (outer `v`): uniform `z`-box
-/

/-- A uniform interval containing every `zSetV td v` (Step 4), ignoring dependence on `u₀(v)`. -/
def zBoxV (td : TubeData) : Finset ℤ :=
  Finset.Icc
    (⌊((-td.U - (td.q : ℝ)) / (td.q : ℝ))⌋ : ℤ)
    (⌈(td.U) / (td.q : ℝ)⌉ : ℤ)

theorem mem_zSetV_imp_mem_zBoxV (td : TubeData) {v z : ℤ} (hz : z ∈ zSetV td v) :
    z ∈ zBoxV td := by
  classical
  have hq : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
  have hzI : z ∈
      (Finset.Icc
        (⌊((-td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌋ : ℤ)
        (⌈((td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌉ : ℤ)) :=
    mem_zSetV_imp_mem_Icc_floor_ceil (td := td) (v := v) (z := z) hz
  have hzI' :
      (⌊((-td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌋ : ℤ) ≤ z ∧
        z ≤ (⌈((td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌉ : ℤ) := by
    simpa [Finset.mem_Icc] using hzI
  -- `u₀(v) < q` gives `-U - q ≤ -U - u₀(v)`.
  have hu0_le_q : (uResidue td v : ℝ) ≤ (td.q : ℝ) := by
    have : (uResidue td v : ℝ) < (td.q : ℝ) := by
      exact_mod_cast (uResidue_lt td v)
    exact le_of_lt this
  have hleft_le :
      (⌊((-td.U - (td.q : ℝ)) / (td.q : ℝ))⌋ : ℤ)
        ≤
      (⌊((-td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌋ : ℤ) := by
    have hnum : (-td.U - (td.q : ℝ)) ≤ (-td.U - (uResidue td v : ℤ)) := by
      have : -(td.q : ℝ) ≤ -(uResidue td v : ℝ) := neg_le_neg hu0_le_q
      linarith
    have hdiv :
        (-td.U - (td.q : ℝ)) / (td.q : ℝ) ≤ (-td.U - (uResidue td v : ℤ)) / (td.q : ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hq)
    exact Int.floor_mono hdiv
  have hz_left : (⌊((-td.U - (td.q : ℝ)) / (td.q : ℝ))⌋ : ℤ) ≤ z := le_trans hleft_le hzI'.1
  -- `0 ≤ u₀(v)` gives `U - u₀(v) ≤ U`.
  have hu0_nonneg : (0 : ℝ) ≤ (uResidue td v : ℝ) := by
    exact_mod_cast (uResidue_nonneg td v)
  have hright_le :
      (⌈((td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌉ : ℤ)
        ≤
      (⌈(td.U) / (td.q : ℝ)⌉ : ℤ) := by
    have hnum : (td.U - (uResidue td v : ℤ)) ≤ td.U := by
      linarith [hu0_nonneg]
    have hdiv :
        (td.U - (uResidue td v : ℤ)) / (td.q : ℝ) ≤ td.U / (td.q : ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hq)
    exact Int.ceil_mono hdiv
  have hz_right : z ≤ (⌈(td.U) / (td.q : ℝ)⌉ : ℤ) := le_trans hzI'.2 hright_le
  simpa [zBoxV, Finset.mem_Icc] using And.intro hz_left hz_right

theorem zSetV_subset_zBoxV (td : TubeData) (v : ℤ) : zSetV td v ⊆ zBoxV td := by
  intro z hz
  exact mem_zSetV_imp_mem_zBoxV (td := td) (v := v) (z := z) hz

end IndexBounds

end

end LargeSieve
end TypeII
end Engines
end SSU
