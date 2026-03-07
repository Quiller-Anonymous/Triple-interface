import SSU.Engines.LargeSieve.TypeIIFiberEnergy
import SSU.Engines.LargeSieve.TypeIIZSetCard
import SSU.Engines.LargeSieve.TypeIIZSetVCard
import SSU.Engines.LargeSieve.TypeIIStep3Reduce
import SSU.Engines.LargeSieve.TypeIIStep4Reduce

/-!
Montgomery–Vaughan large sieve: TeX-faithful specializations for the Type–II Step 3/4 fibers.

This file bridges the *analytic* large sieve statement (still packaged as hypotheses) into the
already-implemented deterministic Step 3/4 reduction scaffolds.

Concretely:
* Step 3 (LS-outer-u): a large sieve bound for `innerSumUZ` over `u`;
* Step 4 (LS-outer-v): a large sieve bound for `innerSumVZ` over `v`;
and in both cases we use deterministic tube geometry to replace coefficient energy by
`tubeEnergy`.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

namespace LargeSieve

/-!
## Step 3: MV hypothesis → `Step3FiberLargeSieve`

We package the Montgomery–Vaughan large sieve in the exact *shape* needed by the TeX Step 3 fiber
bound. This is the first “non-toy” analytic hypothesis that will later be replaced by a proof.
-/

structure Step3MontgomeryVaughan (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
          ≤
        C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
        (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2))

/-!
### TeX-faithful refinement: prove Step 3 *per residue class*

In `05b_SSU.tex`, Step 3 first fixes the congruence class (equivalently, fixes `v₀(u) ∈ [0,q)`)
and works on the corresponding arithmetic progression.  For later proofs, it is convenient to
package that as a hypothesis *per residue class* and then sum over residues.

This section is still purely deterministic: it just repackages the Step 3 interface.
-/

/-- A per-residue-class version of `Step3MontgomeryVaughan`: the same inequality but with the
outer sum restricted to a single class `uClass td r`. -/
structure Step3MontgomeryVaughanByResidue (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        ∀ r ∈ ResiduePartition.residuesU td,
          (∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2)
            ≤
          C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
            (∑ u ∈ ResiduePartition.uClass td r,
              ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2))

/-- Per-residue Step 3 from a `zSet` cardinality envelope (deterministic Cauchy–Schwarz route). -/
def Step3MontgomeryVaughanByResidue.of_card_zSet
    (td : TubeData) (Cz : ℝ)
    (hCz : 0 ≤ Cz)
    (hcard : ∀ u : ℤ, ((zSet td u).card : ℝ) ≤ Cz * (td.D / (td.q : ℝ)))
    (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) :
    Step3MontgomeryVaughanByResidue td :=
by
  classical
  refine ⟨Cz, hCz, ?_⟩
  intro ξ hξ0 _hξH F r hr
  have hinner (u : ℤ) :
      ‖innerSumUZ td ξ F u‖ ^ 2
        ≤
      ((zSet td u).card : ℝ) *
        (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
    have hcs :=
      (norm_sum_sq_le_card_mul_sum_norm_sq (s := zSet td u)
        (f := fun z : ℤ =>
          (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X)))
    have hsimp :
        (∑ z ∈ zSet td u,
            (‖∑ p ∈ fiberUZ td u z, F p‖ *
                ‖e (ξ * (u : ℝ) * (z : ℝ) / td.X)‖) ^ 2)
          =
        ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      simp [norm_e]
    simpa [LargeSieve.innerSumUZ, hsimp] using hcs
  have hsum :
      (∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2)
        ≤
      ∑ u ∈ ResiduePartition.uClass td r,
        ((zSet td u).card : ℝ) *
          (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro u hu
    exact hinner u
  have hsum' :
      (∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2)
        ≤
      (Cz * (td.D / (td.q : ℝ))) *
        (∑ u ∈ ResiduePartition.uClass td r,
          ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
    have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have hDq : 0 ≤ td.D / (td.q : ℝ) := div_nonneg hD (le_of_lt hq)
    have hcoeff_nonneg (u : ℤ) :
        0 ≤ (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 : ℝ) := by
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    have hpoint (u : ℤ) :
        ((zSet td u).card : ℝ) *
            (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
          ≤
        (Cz * (td.D / (td.q : ℝ))) *
            (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_right (hcard u) (hcoeff_nonneg u)
    calc
      (∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2)
          ≤
        ∑ u ∈ ResiduePartition.uClass td r,
          ((zSet td u).card : ℝ) *
            (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := hsum
      _ ≤
        ∑ u ∈ ResiduePartition.uClass td r,
          (Cz * (td.D / (td.q : ℝ))) *
            (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro u hu
          exact hpoint u
      _ =
        (Cz * (td.D / (td.q : ℝ))) *
          (∑ u ∈ ResiduePartition.uClass td r,
            ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
          simp [Finset.mul_sum, mul_assoc]
  have hUx : 1 ≤ td.U + td.X / |ξ| := by
    have hx : 0 ≤ td.X / |ξ| := div_nonneg hX (abs_nonneg ξ)
    nlinarith [hU, hx]
  have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
  have hDq : 0 ≤ td.D / (td.q : ℝ) := div_nonneg hD (le_of_lt hq)
  have hcoeff_nonneg :
      0 ≤ (∑ u ∈ ResiduePartition.uClass td r,
            ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 : ℝ) := by
    refine Finset.sum_nonneg ?_
    intro u hu
    refine Finset.sum_nonneg ?_
    intro z hz
    positivity
  have :
      (Cz * (td.D / (td.q : ℝ))) *
          (∑ u ∈ ResiduePartition.uClass td r,
            ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        ≤
      Cz * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
          (∑ u ∈ ResiduePartition.uClass td r,
            ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := by
    have hmono :
        (Cz * (td.D / (td.q : ℝ))) *
            (∑ u ∈ ResiduePartition.uClass td r,
              ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
          ≤
        (Cz * (td.D / (td.q : ℝ))) * ((td.U + td.X / |ξ|) *
            (∑ u ∈ ResiduePartition.uClass td r,
              ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCz hDq)
      simpa [mul_assoc] using (le_mul_of_one_le_left hcoeff_nonneg hUx)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmono
  exact le_trans hsum' this

/-- Broad geometric per-residue Step 3 route, valid without any `q ≤ D` assumption. -/
def Step3MontgomeryVaughanByResidue.of_general_geometry (td : TubeData)
    (hDpos : 0 < td.D) (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) :
    Step3MontgomeryVaughanByResidue td :=
by
  let qR : ℝ := (td.q : ℝ)
  let Dq : ℝ := td.D / qR
  let qD : ℝ := qR / td.D
  let Cz : ℝ := 3 * max 1 qD
  have hqRpos : 0 < qR := by
    dsimp [qR]
    exact_mod_cast td.q_pos
  have hCz : 0 ≤ Cz := by
    have hq0 : 0 ≤ qR := le_of_lt hqRpos
    have hqD0 : 0 ≤ qD := div_nonneg hq0 (le_of_lt hDpos)
    have hmax0 : 0 ≤ max 1 qD := by exact le_trans (by norm_num) (le_max_left _ _)
    nlinarith
  refine Step3MontgomeryVaughanByResidue.of_card_zSet
    (td := td) (Cz := Cz) (hCz := hCz) (hcard := ?_) (hD := hD) (hU := hU) (hX := hX)
  intro u
  have hcard2 :
      ((zSet td u).card : ℝ) ≤ (td.D / (td.q : ℝ)) + 2 :=
    SSU.Engines.TypeII.LargeSieve.card_zSet_le_D_div_q_add_two (td := td) (u := u) hD
  have hDq0 : 0 ≤ Dq := div_nonneg hD (le_of_lt hqRpos)
  by_cases hDq_ge_one : 1 ≤ Dq
  · have hcard3Dq : ((zSet td u).card : ℝ) ≤ 3 * Dq := by
      have hcard2' : ((zSet td u).card : ℝ) ≤ Dq + 2 := by simpa [Dq, qR] using hcard2
      have hDq_step : Dq + 2 ≤ 3 * Dq := by nlinarith [hDq_ge_one]
      exact hcard2'.trans hDq_step
    have hCz_ge_three : 3 ≤ Cz := by
      have hmax_ge : (1 : ℝ) ≤ max 1 qD := le_max_left _ _
      dsimp [Cz]
      nlinarith
    have hmul : 3 * Dq ≤ Cz * Dq := by
      exact mul_le_mul_of_nonneg_right hCz_ge_three hDq0
    exact hcard3Dq.trans hmul
  · have hDq_lt_one : Dq < 1 := lt_of_not_ge hDq_ge_one
    have hcard3 : ((zSet td u).card : ℝ) ≤ 3 := by
      have hcard2' : ((zSet td u).card : ℝ) ≤ Dq + 2 := by simpa [Dq, qR] using hcard2
      nlinarith [hcard2', hDq_lt_one]
    have hqD_gt_one : 1 < qD := by
      have hD_lt_q : td.D < qR := (div_lt_one hqRpos).1 hDq_lt_one
      exact (one_lt_div hDpos).2 hD_lt_q
    have hmax_eq : max 1 qD = qD := max_eq_right (le_of_lt hqD_gt_one)
    have hqRne' : (td.q : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt td.q_pos)
    have hDne : td.D ≠ 0 := ne_of_gt hDpos
    have hqD_mul : qD * Dq = 1 := by
      dsimp [qD, Dq, qR]
      field_simp [hqRne', hDne]
    have hCz_mul : Cz * Dq = 3 := by
      calc
        Cz * Dq = (3 * max 1 qD) * Dq := by rfl
        _ = 3 * (qD * Dq) := by
              simp [hmax_eq, mul_assoc, mul_left_comm, mul_comm]
        _ = 3 := by simp [hqD_mul]
    calc
      ((zSet td u).card : ℝ) ≤ 3 := hcard3
      _ = Cz * Dq := by simpa [hCz_mul]

/-- Sum the per-residue Step 3 hypothesis to obtain the global `Step3MontgomeryVaughan`. -/
def Step3MontgomeryVaughan.of_byResidue
    (td : TubeData) (hR : Step3MontgomeryVaughanByResidue td) :
    Step3MontgomeryVaughan td :=
by
  classical
  refine ⟨hR.C, hR.C_nonneg, ?_⟩
  intro ξ hξ0 hξH F
  -- Use the deterministic residue partition on both sides.
  have hL :
      (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
        =
      ∑ r ∈ ResiduePartition.residuesU td,
        ∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2 := by
    simpa using
      (sum_uSet_norm_innerSumUZ_sq_eq_sum_residueClasses (td := td) (ξ := ξ) (F := F))
  have hE :
      (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        =
      ∑ r ∈ ResiduePartition.residuesU td,
        ∑ u ∈ ResiduePartition.uClass td r,
          ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 := by
    simpa using
      (ResiduePartition.sum_uSet_eq_sum_residueClasses (td := td)
        (f := fun u : ℤ => ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2))
  -- Sum the per-residue bounds.
  have hsum :
      (∑ r ∈ ResiduePartition.residuesU td,
        ∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2)
        ≤
      ∑ r ∈ ResiduePartition.residuesU td,
        hR.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
          (∑ u ∈ ResiduePartition.uClass td r,
            ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := by
    refine Finset.sum_le_sum ?_
    intro r hr
    exact hR.bound ξ hξ0 hξH F r hr
  -- Factor out the constant.
  calc
    (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
        = ∑ r ∈ ResiduePartition.residuesU td,
            ∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2 := hL
    _ ≤ ∑ r ∈ ResiduePartition.residuesU td,
          hR.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
            (∑ u ∈ ResiduePartition.uClass td r,
              ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := hsum
    _ =
        hR.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
          (∑ r ∈ ResiduePartition.residuesU td,
            ∑ u ∈ ResiduePartition.uClass td r,
              ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = hR.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
          (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := by
          simpa [hE]

/-!
### A deterministic fallback: Cauchy–Schwarz in the inner `z`-sum

This is **not** the Montgomery–Vaughan large sieve. It is a helper lemma that turns a *purely
geometric* uniform bound on the cardinality of each `zSet td u` into a `Step3MontgomeryVaughan`
instance by a single Cauchy–Schwarz application.

It is useful as a micro-step because it lets us separate the analytic work (proving a strong large
sieve) from the deterministic work (bounding the number of `z` in the progression), while still
producing an object of the exact TeX interface type.
-/

def Step3MontgomeryVaughan.of_card_zSet
    (td : TubeData) (Cz : ℝ)
    (hCz : 0 ≤ Cz)
    (hcard : ∀ u : ℤ, ((zSet td u).card : ℝ) ≤ Cz * (td.D / (td.q : ℝ)))
    (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) :
    Step3MontgomeryVaughan td :=
by
  classical
  refine ⟨Cz, hCz, ?_⟩
  intro ξ hξ0 _hξH F
  -- Pointwise `u`: apply Cauchy–Schwarz in the inner `z`-sum.
  have hinner (u : ℤ) :
      ‖innerSumUZ td ξ F u‖ ^ 2
        ≤
      ((zSet td u).card : ℝ) *
        (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
    -- Apply `‖∑ f‖² ≤ card * ∑ ‖f‖²` to `f z = coeff(u,z) * e(...)`.
    have hcs :=
      (norm_sum_sq_le_card_mul_sum_norm_sq (s := zSet td u)
        (f := fun z : ℤ =>
          (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X)))
    -- Drop the unimodular phase from the norm:
    -- `‖coeff * e(·)‖ = ‖coeff‖ * ‖e(·)‖ = ‖coeff‖`.
    have hsimp :
        (∑ z ∈ zSet td u,
            (‖∑ p ∈ fiberUZ td u z, F p‖ *
                ‖e (ξ * (u : ℝ) * (z : ℝ) / td.X)‖) ^ 2)
          =
        ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      simp [norm_e]
    -- `innerSumUZ` is exactly this inner `z`-sum.
    simpa [LargeSieve.innerSumUZ, hsimp] using hcs

  -- Sum over `u ∈ uSet td`.
  have hsum :
      (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
        ≤
      ∑ u ∈ uSet td,
        ((zSet td u).card : ℝ) *
          (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro u hu
    exact hinner u

  -- Replace `card(zSet)` by the geometric bound `Cz * (D/q)`.
  have hsum' :
      (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
        ≤
      (Cz * (td.D / (td.q : ℝ))) *
        (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
    have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have hDq : 0 ≤ td.D / (td.q : ℝ) := div_nonneg hD (le_of_lt hq)
    have hC : 0 ≤ Cz * (td.D / (td.q : ℝ)) := mul_nonneg hCz hDq
    have hcoeff_nonneg (u : ℤ) :
        0 ≤ (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 : ℝ) := by
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    -- Pointwise bound in `u`.
    have hpoint (u : ℤ) :
        ((zSet td u).card : ℝ) *
            (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
          ≤
        (Cz * (td.D / (td.q : ℝ))) *
            (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
      exact
        mul_le_mul_of_nonneg_right (hcard u) (hcoeff_nonneg u)
    -- Sum and factor out the constant.
    calc
      (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
          ≤
        ∑ u ∈ uSet td,
          ((zSet td u).card : ℝ) *
            (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := hsum
      _ ≤
        ∑ u ∈ uSet td,
          (Cz * (td.D / (td.q : ℝ))) *
            (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
              refine Finset.sum_le_sum ?_
              intro u hu
              exact hpoint u
      _ =
        (Cz * (td.D / (td.q : ℝ))) *
          (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
            simp [Finset.mul_sum, mul_assoc]

  -- Insert the TeX factor `(U + X/|ξ|)` using `1 ≤ U` and `X/|ξ| ≥ 0`.
  have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
  have hDq : 0 ≤ td.D / (td.q : ℝ) := div_nonneg hD (le_of_lt hq)
  have hUx : 1 ≤ td.U + td.X / |ξ| := by
    have hx : 0 ≤ td.X / |ξ| := div_nonneg hX (abs_nonneg ξ)
    nlinarith [hU, hx]
  have hcoeff_nonneg :
      0 ≤ (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 : ℝ) := by
    refine Finset.sum_nonneg ?_
    intro u hu
    refine Finset.sum_nonneg ?_
    intro z hz
    positivity
  -- Monotonicity in the extra nonnegative factor.
  have hmono :
      (Cz * (td.D / (td.q : ℝ))) *
          (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        ≤
      Cz * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
        (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := by
    -- Rewrite the RHS to expose the same product ordering.
    have : Cz * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
        (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2))
          =
        (Cz * (td.D / (td.q : ℝ))) * ((td.U + td.X / |ξ|) *
          (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := by
      ring
    -- Use `1 ≤ (U + X/|ξ|)` and nonnegativity of the remaining factors.
    have hC : 0 ≤ Cz * (td.D / (td.q : ℝ)) := mul_nonneg hCz hDq
    calc
      (Cz * (td.D / (td.q : ℝ))) *
          (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
          ≤
        (Cz * (td.D / (td.q : ℝ))) *
          ((td.U + td.X / |ξ|) *
            (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := by
              -- multiply `S ≤ (U+...)*S` by the nonnegative constant.
              refine mul_le_mul_of_nonneg_left ?_ hC
              -- `S ≤ (U+...)*S` since `1 ≤ U+...` and `S ≥ 0`.
              have : (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 : ℝ)
                        ≤
                      (td.U + td.X / |ξ|) *
                        (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 : ℝ) := by
                have hpos : 0 ≤ (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 : ℝ) :=
                  hcoeff_nonneg
                nlinarith [hUx, hpos]
              simpa [mul_assoc] using this
      _ = Cz * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
          (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := by
            simpa [this]

  exact hsum'.trans hmono

/-!
### A first geometric instantiation (still “analytic-trivial”)

Combining the deterministic `zSet` cardinality bound (coming only from `D < d ≤ 2D`) with
`Step3MontgomeryVaughan.of_card_zSet` gives a concrete Step 3 hypothesis whose constant is `C = 3`.

This is **not** the large sieve: it is a fallback bound that is sufficient as a scaffold and is
useful for testing that the Step 3/4/5 plumbing runs end-to-end without assuming any deep
analytic input.
-/

def Step3MontgomeryVaughan.of_box_geometry (td : TubeData)
    (hDq : 1 ≤ td.D / (td.q : ℝ)) (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) :
    Step3MontgomeryVaughan td :=
by
  -- Use `Cz = 3` and the deterministic bound `card(zSet) ≤ 3*(D/q)`.
  refine Step3MontgomeryVaughan.of_card_zSet
      (td := td) (Cz := 3) (hCz := by norm_num)
      (hcard := fun u => by
        -- `card(zSet td u) ≤ 3 * (D/q)`.
        simpa [mul_assoc] using
          (SSU.Engines.TypeII.LargeSieve.card_zSet_le_three_mul_D_div_q (td := td) (u := u) hDq hD))
      (hD := hD) (hU := hU) (hX := hX)

/-- Broad geometric Step 3 fallback with no `q ≤ D` requirement.

This uses the universal deterministic bound `card(zSet) ≤ D/q + 2` and absorbs the additive
`+2` into a parameter-only multiplicative constant. -/
def Step3MontgomeryVaughan.of_general_geometry (td : TubeData)
    (hDpos : 0 < td.D) (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) :
    Step3MontgomeryVaughan td :=
by
  let qR : ℝ := (td.q : ℝ)
  let Dq : ℝ := td.D / qR
  let qD : ℝ := qR / td.D
  let Cz : ℝ := 3 * max 1 qD
  have hqRpos : 0 < qR := by
    dsimp [qR]
    exact_mod_cast td.q_pos
  have hCz : 0 ≤ Cz := by
    have hq0 : 0 ≤ qR := le_of_lt hqRpos
    have hqD0 : 0 ≤ qD := div_nonneg hq0 (le_of_lt hDpos)
    have hmax0 : 0 ≤ max 1 qD := by exact le_trans (by norm_num) (le_max_left _ _)
    nlinarith
  refine Step3MontgomeryVaughan.of_card_zSet
    (td := td) (Cz := Cz) (hCz := hCz) (hcard := ?_) (hD := hD) (hU := hU) (hX := hX)
  intro u
  have hcard2 :
      ((zSet td u).card : ℝ) ≤ (td.D / (td.q : ℝ)) + 2 :=
    SSU.Engines.TypeII.LargeSieve.card_zSet_le_D_div_q_add_two (td := td) (u := u) hD
  have hDq0 : 0 ≤ Dq := div_nonneg hD (le_of_lt hqRpos)
  by_cases hDq_ge_one : 1 ≤ Dq
  · have hcard3Dq : ((zSet td u).card : ℝ) ≤ 3 * Dq := by
      have hcard2' : ((zSet td u).card : ℝ) ≤ Dq + 2 := by simpa [Dq, qR] using hcard2
      have hDq_step : Dq + 2 ≤ 3 * Dq := by nlinarith [hDq_ge_one]
      exact hcard2'.trans hDq_step
    have hCz_ge_three : 3 ≤ Cz := by
      have hmax_ge : (1 : ℝ) ≤ max 1 qD := le_max_left _ _
      dsimp [Cz]
      nlinarith
    have hmul : 3 * Dq ≤ Cz * Dq := by
      exact mul_le_mul_of_nonneg_right hCz_ge_three hDq0
    exact hcard3Dq.trans hmul
  · have hDq_lt_one : Dq < 1 := lt_of_not_ge hDq_ge_one
    have hcard3 : ((zSet td u).card : ℝ) ≤ 3 := by
      have hcard2' : ((zSet td u).card : ℝ) ≤ Dq + 2 := by simpa [Dq, qR] using hcard2
      nlinarith [hcard2', hDq_lt_one]
    have hqD_gt_one : 1 < qD := by
      have hD_lt_q : td.D < qR := (div_lt_one hqRpos).1 hDq_lt_one
      exact (one_lt_div hDpos).2 hD_lt_q
    have hmax_eq : max 1 qD = qD := max_eq_right (le_of_lt hqD_gt_one)
    have hqRne' : (td.q : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt td.q_pos)
    have hDne : td.D ≠ 0 := ne_of_gt hDpos
    have hqD_mul : qD * Dq = 1 := by
      dsimp [qD, Dq, qR]
      field_simp [hqRne', hDne]
    have hCz_mul : Cz * Dq = 3 := by
      calc
        Cz * Dq = (3 * max 1 qD) * Dq := by rfl
        _ = 3 * (qD * Dq) := by
              simp [hmax_eq, mul_assoc, mul_left_comm, mul_comm]
        _ = 3 := by simp [hqD_mul]
    calc
      ((zSet td u).card : ℝ) ≤ 3 := hcard3
      _ = Cz * Dq := by simpa [hCz_mul]

def step3FiberLargeSieve_of_montgomeryVaughan (td : TubeData) (hMV : Step3MontgomeryVaughan td)
    (_hD : 0 ≤ td.D) (_hU : 0 ≤ td.U) (_hX : 0 ≤ td.X) : Step3FiberLargeSieve td := by
  classical
  refine ⟨hMV.C, hMV.C_nonneg, ?_⟩
  intro ξ hξ0 hξH F
  have hcoeff :
      (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        =
      tubeEnergy td.T F :=
    sum_u_z_norm_fiberUZ_sum_sq_eq_tubeEnergy (td := td) (F := F)
  have hMV' := hMV.bound ξ hξ0 hξH F
  calc
    (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
        ≤
      hMV.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
        (∑ u ∈ uSet td, ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) := hMV'
    _ = hMV.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F) := by
          simpa [hcoeff, mul_assoc, mul_left_comm, mul_comm]

/-!
## Step 4: MV hypothesis → `Step4FiberLargeSieve`
-/

structure Step4MontgomeryVaughan (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
          ≤
        C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
          (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2))

/-!
### TeX-faithful refinement: prove Step 4 *per residue class*

This is the `v`-analogue of `Step3MontgomeryVaughanByResidue`: restrict the outer sum to a single
congruence class `uResidue td v ∈ [0,q)` and then sum over residues.
-/

structure Step4MontgomeryVaughanByResidue (td : TubeData) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        ∀ r ∈ ResiduePartitionV.residuesV td,
          (∑ v ∈ ResiduePartitionV.vClass td r, ‖innerSumVZ td ξ F v‖ ^ 2)
            ≤
          C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
            (∑ v ∈ ResiduePartitionV.vClass td r,
              ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2))

def Step4MontgomeryVaughan.of_byResidue
    (td : TubeData) (hR : Step4MontgomeryVaughanByResidue td) :
    Step4MontgomeryVaughan td :=
by
  classical
  refine ⟨hR.C, hR.C_nonneg, ?_⟩
  intro ξ hξ0 hξH F
  have hL :
      (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
        =
      ∑ r ∈ ResiduePartitionV.residuesV td,
        ∑ v ∈ ResiduePartitionV.vClass td r, ‖innerSumVZ td ξ F v‖ ^ 2 := by
    simpa using
      (sum_vSet_norm_innerSumVZ_sq_eq_sum_residueClasses (td := td) (ξ := ξ) (F := F))
  have hE :
      (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
        =
      ∑ r ∈ ResiduePartitionV.residuesV td,
        ∑ v ∈ ResiduePartitionV.vClass td r,
          ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 := by
    simpa using
      (ResiduePartitionV.sum_vSet_eq_sum_residueClasses (td := td)
        (f := fun v : ℤ => ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2))
  have hsum :
      (∑ r ∈ ResiduePartitionV.residuesV td,
        ∑ v ∈ ResiduePartitionV.vClass td r, ‖innerSumVZ td ξ F v‖ ^ 2)
        ≤
      ∑ r ∈ ResiduePartitionV.residuesV td,
        hR.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
          (∑ v ∈ ResiduePartitionV.vClass td r,
            ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)) := by
    refine Finset.sum_le_sum ?_
    intro r hr
    exact hR.bound ξ hξ0 hξH F r hr
  calc
    (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
        = ∑ r ∈ ResiduePartitionV.residuesV td,
            ∑ v ∈ ResiduePartitionV.vClass td r, ‖innerSumVZ td ξ F v‖ ^ 2 := hL
    _ ≤ ∑ r ∈ ResiduePartitionV.residuesV td,
          hR.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
            (∑ v ∈ ResiduePartitionV.vClass td r,
              ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)) := hsum
    _ =
        hR.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
          (∑ r ∈ ResiduePartitionV.residuesV td,
            ∑ v ∈ ResiduePartitionV.vClass td r,
              ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = hR.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
          (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)) := by
          simpa [hE]

/-- Deterministic per-residue Step 4 route from pure tube geometry (`|u| ≤ U`). -/
def Step4MontgomeryVaughanByResidue.of_box_geometry (td : TubeData)
    (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hXH1 : 1 ≤ td.X * td.H) :
    Step4MontgomeryVaughanByResidue td :=
by
  classical
  refine ⟨(2 * td.U) / (td.q : ℝ) + 3, ?_, ?_⟩
  · have hq : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have : 0 ≤ (2 * td.U) / (td.q : ℝ) := by
      exact div_nonneg (by nlinarith [hU]) (le_of_lt hq)
    nlinarith
  · intro ξ _hξ0 _hξH F r hr
    have hinner (v : ℤ) :
        ‖innerSumVZ td ξ F v‖ ^ 2
          ≤
        (((2 * td.U) / (td.q : ℝ) + 3)) *
          (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
      have hcs :=
        (norm_sum_sq_le_card_mul_sum_norm_sq (s := zSetV td v)
          (f := fun z : ℤ =>
            (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X)))
      have hsimp :
          (∑ z ∈ zSetV td v,
              (‖∑ p ∈ fiberVZ td v z, F p‖ * ‖e (ξ * (z : ℝ) * (v : ℝ) / td.X)‖) ^ 2)
            =
          ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro z hz
        simp [norm_e]
      have h0 :
          ‖innerSumVZ td ξ F v‖ ^ 2
            ≤
          ((zSetV td v).card : ℝ) *
            (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
        simpa [LargeSieve.innerSumVZ, hsimp] using hcs
      have hcard :
          ((zSetV td v).card : ℝ) ≤ ((2 * td.U) / (td.q : ℝ) + 3) := by
        simpa using
          (SSU.Engines.TypeII.LargeSieve.card_zSetV_le_two_mul_U_div_q_add_three
            (td := td) (v := v) hU)
      have hcoeff_nonneg :
          0 ≤ (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 : ℝ) := by
        refine Finset.sum_nonneg ?_
        intro z hz
        positivity
      exact le_trans h0 (by
        have := mul_le_mul_of_nonneg_right hcard hcoeff_nonneg
        simpa [mul_assoc, mul_left_comm, mul_comm] using this)
    have hsum :
        (∑ v ∈ ResiduePartitionV.vClass td r, ‖innerSumVZ td ξ F v‖ ^ 2)
          ≤
        (((2 * td.U) / (td.q : ℝ) + 3)) *
          (∑ v ∈ ResiduePartitionV.vClass td r,
            ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
      calc
        (∑ v ∈ ResiduePartitionV.vClass td r, ‖innerSumVZ td ξ F v‖ ^ 2)
            ≤
          ∑ v ∈ ResiduePartitionV.vClass td r, (((2 * td.U) / (td.q : ℝ) + 3)) *
            (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
              refine Finset.sum_le_sum ?_
              intro v hv
              exact hinner v
        _ =
          (((2 * td.U) / (td.q : ℝ) + 3)) *
            (∑ v ∈ ResiduePartitionV.vClass td r,
              ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
              simp [Finset.mul_sum, mul_assoc]
    have hqpos : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have hUq_nonneg : 0 ≤ td.U / (td.q : ℝ) := by
      exact div_nonneg hU (le_of_lt hqpos)
    have habspos : 0 < |ξ| := abs_pos.2 _hξ0
    have hH_le_invabs : td.H ≤ 1 / |ξ| := by
      have hinv : 1 / (1 / td.H) ≤ 1 / |ξ| := one_div_le_one_div_of_le habspos _hξH
      simpa [one_div] using hinv
    have hXH_le : td.X * td.H ≤ td.X / |ξ| := by
      have := mul_le_mul_of_nonneg_left hH_le_invabs hX
      simpa [div_eq_mul_inv, mul_assoc] using this
    have hX_over_abs_ge_one : 1 ≤ td.X / |ξ| := le_trans hXH1 hXH_le
    have hUx_ge_one : 1 ≤ td.U / (td.q : ℝ) + td.X / |ξ| := by
      have hxle : td.X / |ξ| ≤ td.U / (td.q : ℝ) + td.X / |ξ| := le_add_of_nonneg_left hUq_nonneg
      exact hX_over_abs_ge_one.trans hxle
    have hD_nonneg : 0 ≤ td.D := le_trans (by linarith) hD1
    have hfactor_ge_one : 1 ≤ td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) := by
      nlinarith [hD1, hUx_ge_one]
    have hS_nonneg :
        0 ≤ (∑ v ∈ ResiduePartitionV.vClass td r,
              ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 : ℝ) := by
      refine Finset.sum_nonneg ?_
      intro v hv
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    have hS_le :
        (∑ v ∈ ResiduePartitionV.vClass td r,
            ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 : ℝ)
          ≤
        td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
          (∑ v ∈ ResiduePartitionV.vClass td r,
            ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 : ℝ) := by
      nlinarith [hfactor_ge_one, hS_nonneg]
    have hC_nonneg :
        0 ≤ ((2 * td.U) / (td.q : ℝ) + 3 : ℝ) := by
      have : 0 ≤ (2 * td.U) / (td.q : ℝ) := by
        exact div_nonneg (by nlinarith [hU]) (le_of_lt hqpos)
      nlinarith
    have hmono :
        (((2 * td.U) / (td.q : ℝ) + 3 : ℝ) *
            (∑ v ∈ ResiduePartitionV.vClass td r,
              ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2))
          ≤
        (((2 * td.U) / (td.q : ℝ) + 3 : ℝ) *
            (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
              (∑ v ∈ ResiduePartitionV.vClass td r,
                ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2))) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hS_le hC_nonneg)
    exact hsum.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmono)

/-- Deterministic fallback Step 4 MV hypothesis from pure tube geometry (`|u| ≤ U`). -/
def Step4MontgomeryVaughan.of_box_geometry (td : TubeData)
    (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hXH1 : 1 ≤ td.X * td.H) :
    Step4MontgomeryVaughan td :=
by
  classical
  -- Use the crude bound `card(zSetV) ≤ 2U/q + 3` and Cauchy–Schwarz in the inner `z`-sum.
  refine ⟨(2 * td.U) / (td.q : ℝ) + 3, ?_, ?_⟩
  · have hq : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have : 0 ≤ (2 * td.U) / (td.q : ℝ) := by
      exact div_nonneg (by nlinarith [hU]) (le_of_lt hq)
    nlinarith
  · intro ξ _hξ0 _hξH F
    -- Pointwise `v`: Cauchy–Schwarz in the inner `z`-sum, then use the cardinality bound.
    have hinner (v : ℤ) :
        ‖innerSumVZ td ξ F v‖ ^ 2
          ≤
        (((2 * td.U) / (td.q : ℝ) + 3)) *
          (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
      -- `‖∑_z a_z e(...)‖² ≤ card(zSetV) * ∑ ‖a_z‖²` and `card(zSetV) ≤ 2U/q+3`.
      have hcs :=
        (norm_sum_sq_le_card_mul_sum_norm_sq (s := zSetV td v)
          (f := fun z : ℤ =>
            (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X)))
      have hsimp :
          (∑ z ∈ zSetV td v,
              (‖∑ p ∈ fiberVZ td v z, F p‖ * ‖e (ξ * (z : ℝ) * (v : ℝ) / td.X)‖) ^ 2)
            =
          ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro z hz
        simp [norm_e]
      have h0 :
          ‖innerSumVZ td ξ F v‖ ^ 2
            ≤
          ((zSetV td v).card : ℝ) *
            (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
        simpa [LargeSieve.innerSumVZ, hsimp] using hcs
      have hcard :
          ((zSetV td v).card : ℝ) ≤ ((2 * td.U) / (td.q : ℝ) + 3) := by
        simpa using
          (SSU.Engines.TypeII.LargeSieve.card_zSetV_le_two_mul_U_div_q_add_three (td := td) (v := v) hU)
      have hcoeff_nonneg :
          0 ≤ (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 : ℝ) := by
        refine Finset.sum_nonneg ?_
        intro z hz
        positivity
      -- Multiply by the nonnegative coefficient energy.
      exact le_trans h0 (by
        have := mul_le_mul_of_nonneg_right hcard hcoeff_nonneg
        -- reorder factors
        simpa [mul_assoc, mul_left_comm, mul_comm] using this)

    -- Sum in `v` to get the full Step 4 MV bound.
    have hsum :
        (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
          ≤
        (((2 * td.U) / (td.q : ℝ) + 3)) *
          (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
      calc
        (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
            ≤
          ∑ v ∈ vSet td, (((2 * td.U) / (td.q : ℝ) + 3)) *
            (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
              refine Finset.sum_le_sum ?_
              intro v hv
              exact hinner v
        _ =
          (((2 * td.U) / (td.q : ℝ) + 3)) *
            (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
              simp [Finset.mul_sum, mul_assoc]
    -- Insert the TeX prefactor `D * (U/q + X/|ξ|)` by monotonicity (it is ≥ 1 on the ξ-band).
    have hqpos : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have hUq_nonneg : 0 ≤ td.U / (td.q : ℝ) := by
      exact div_nonneg hU (le_of_lt hqpos)
    have habspos : 0 < |ξ| := abs_pos.2 _hξ0
    have hH_le_invabs : td.H ≤ 1 / |ξ| := by
      -- Since `0 < |ξ|` and `|ξ| ≤ 1/H`, taking inverses gives `H ≤ 1/|ξ|`.
      have hinv : 1 / (1 / td.H) ≤ 1 / |ξ| := one_div_le_one_div_of_le habspos _hξH
      simpa [one_div] using hinv
    have hXH_le : td.X * td.H ≤ td.X / |ξ| := by
      have := mul_le_mul_of_nonneg_left hH_le_invabs hX
      -- `td.X * (1/|ξ|) = td.X / |ξ|`.
      simpa [div_eq_mul_inv, mul_assoc] using this
    have hX_over_abs_ge_one : 1 ≤ td.X / |ξ| := le_trans hXH1 hXH_le
    have hUx_ge_one : 1 ≤ td.U / (td.q : ℝ) + td.X / |ξ| := by
      have hxle : td.X / |ξ| ≤ td.U / (td.q : ℝ) + td.X / |ξ| := le_add_of_nonneg_left hUq_nonneg
      exact hX_over_abs_ge_one.trans hxle
    have hD_nonneg : 0 ≤ td.D := le_trans (by linarith) hD1
    have hfactor_ge_one : 1 ≤ td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) := by
      nlinarith [hD1, hUx_ge_one]
    have hS_nonneg :
        0 ≤ (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 : ℝ) := by
      refine Finset.sum_nonneg ?_
      intro v hv
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    have hS_le :
        (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 : ℝ)
          ≤
        td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
          (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 : ℝ) := by
      nlinarith [hfactor_ge_one, hS_nonneg]
    have hC_nonneg :
        0 ≤ ((2 * td.U) / (td.q : ℝ) + 3 : ℝ) := by
      have : 0 ≤ (2 * td.U) / (td.q : ℝ) := by
        exact div_nonneg (by nlinarith [hU]) (le_of_lt hqpos)
      nlinarith
    have hmono :
        (((2 * td.U) / (td.q : ℝ) + 3 : ℝ) *
            (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2))
          ≤
        (((2 * td.U) / (td.q : ℝ) + 3 : ℝ) *
            (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
              (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2))) := by
      -- Multiply the energy inequality by the nonnegative constant `C`.
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hS_le hC_nonneg)

    -- Conclude (this is exactly the `Step4MontgomeryVaughan.bound` shape).
    exact hsum.trans (by
      -- Rewrite to match the goal ordering.
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmono)

def step4FiberLargeSieve_of_montgomeryVaughan (td : TubeData) (hMV : Step4MontgomeryVaughan td)
    (_hD : 0 ≤ td.D) (_hU : 0 ≤ td.U) (_hX : 0 ≤ td.X) : Step4FiberLargeSieve td := by
  classical
  refine ⟨hMV.C, hMV.C_nonneg, ?_⟩
  intro ξ hξ0 hξH F
  have hcoeff :
      (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
        =
      tubeEnergy td.T F :=
    sum_v_z_norm_fiberVZ_sum_sq_eq_tubeEnergy (td := td) (F := F)
  have hMV' := hMV.bound ξ hξ0 hξH F
  calc
    (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
        ≤
      hMV.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
        (∑ v ∈ vSet td, ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)) := hMV'
    _ = hMV.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F) := by
          simpa [hcoeff, mul_assoc, mul_left_comm, mul_comm]

end LargeSieve

end
end TypeII
end Engines
end SSU
