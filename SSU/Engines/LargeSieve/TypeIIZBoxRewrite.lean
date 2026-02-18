import SSU.Engines.LargeSieve.TypeIIStep3Reduce
import SSU.Engines.LargeSieve.TypeIIStep4Reduce
import SSU.Engines.LargeSieve.TypeIIZSetBox
import Mathlib.Data.Int.Interval

/-!
Helper rewrites for TeX Step 3/4:

* enlarge the per-fiber `z`-sum domains `zSet td u` / `zSetV td v` to the uniform supersets
  `zBox td` / `zBoxV td`;
* rewrite the uniform interval sums as translated `range` sums, matching MV's `Fin N` indexing.

This is deterministic algebra; no large sieve inequalities are proved here.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace ZBoxRewrite

open SSU.Engines.TypeII

private theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp [TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Step 3: rewrite `innerSumUZ` as a sum over the uniform `zBox td`. -/
theorem innerSumUZ_eq_sum_zBox (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (u : ℤ) :
    innerSumUZ td ξ F u
      =
    ∑ z ∈ IndexBounds.zBox td,
      (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
  classical
  -- Extend the sum from `zSet` to `zBox` using that the extra fibers are empty.
  have hsub : zSet td u ⊆ IndexBounds.zBox td := by
    intro z hz
    exact IndexBounds.mem_zSet_imp_mem_zBox (td := td) (u := u) (z := z) hz
  have hzero :
      ∀ z ∈ IndexBounds.zBox td, z ∉ zSet td u →
        (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) = 0 := by
    intro z hzBox hzNot
    simp [sum_fiberUZ_eq_zero_of_not_mem_zSet (td := td) (F := F) (u := u) (z := z) hzNot]
  -- Apply `sum_subset` to the `z`-sum.
  have :=
    (Finset.sum_subset hsub (by
      intro z hzBox hzNot
      exact hzero z hzBox hzNot))
  -- Unfold `innerSumUZ` and finish.
  simpa [innerSumUZ] using this

/-- Step 4: rewrite `innerSumVZ` as a sum over the uniform `zBoxV td`. -/
theorem innerSumVZ_eq_sum_zBoxV (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (v : ℤ) :
    innerSumVZ td ξ F v
      =
    ∑ z ∈ IndexBounds.zBoxV td,
      (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
  classical
  have hsub : zSetV td v ⊆ IndexBounds.zBoxV td := by
    intro z hz
    exact IndexBounds.mem_zSetV_imp_mem_zBoxV (td := td) (v := v) (z := z) hz
  have hzero :
      ∀ z ∈ IndexBounds.zBoxV td, z ∉ zSetV td v →
        (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) = 0 := by
    intro z hzBox hzNot
    simp [sum_fiberVZ_eq_zero_of_not_mem_zSetV (td := td) (F := F) (v := v) (z := z) hzNot]
  have :=
    (Finset.sum_subset hsub (by
      intro z hzBox hzNot
      exact hzero z hzBox hzNot))
  simpa [innerSumVZ] using this

/-!
## Interval → range reindexing

These are used to align sums over `IndexBounds.zBox td` / `IndexBounds.zBoxV td` with the MV
`Fin N` indexing (after a translation).
-/

theorem sum_Ioc_eq_sum_range {α : Type*} [AddCommMonoid α] (a b : ℤ) (f : ℤ → α) :
    (∑ z ∈ (Finset.Ioc a b), f z)
      =
    ∑ n ∈ Finset.range (b - a).toNat, f (a + 1 + n) := by
  classical
  -- Expand `Ioc` as a mapped `range` (`Mathlib.Data.Int.Interval`).
  simpa [Int.Ioc_eq_finset_map, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, add_assoc]

theorem sum_Icc_eq_sum_range {α : Type*} [AddCommMonoid α] (a b : ℤ) (f : ℤ → α) :
    (∑ z ∈ (Finset.Icc a b), f z)
      =
    ∑ n ∈ Finset.range (b + 1 - a).toNat, f (a + n) := by
  classical
  simpa [Int.Icc_eq_finset_map, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply]

/-!
### Named endpoints for the uniform boxes

We will later use these to build MV-compatible `Fin N` coefficient arrays by translation.
-/

def zBoxA (td : TubeData) : ℤ :=
  (⌊(td.D - (td.q : ℝ)) / (td.q : ℝ)⌋ : ℤ)

def zBoxB (td : TubeData) : ℤ :=
  (⌈(2 * td.D) / (td.q : ℝ)⌉ : ℤ)

def zBoxN (td : TubeData) : ℕ :=
  (zBoxB td - zBoxA td).toNat

theorem zBox_eq_Icc (td : TubeData) :
    IndexBounds.zBox td = Finset.Icc (zBoxA td + 1) (zBoxB td) := by
  classical
  ext z
  -- `a + 1 ≤ z` is the same as `a < z` over `ℤ`.
  -- After rewriting both memberships, the statement is definitional.
  simp [IndexBounds.zBox, zBoxA, zBoxB, Finset.mem_Ioc, Finset.mem_Icc, Int.add_one_le_iff]

/-!
### Fixed-interval versions of the `zBox` rewrites

These are convenience lemmas: later MV-facing interfaces tend to prefer explicit `Icc` index sets.
-/

/-- Step 3: rewrite `innerSumUZ` as a sum over the explicit interval `Icc (zBoxA+1) zBoxB`. -/
theorem innerSumUZ_eq_sum_Icc_zBox (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (u : ℤ) :
    innerSumUZ td ξ F u
      =
    ∑ z ∈ Finset.Icc (zBoxA td + 1) (zBoxB td),
      (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
  -- Start from the uniform `zBox` form and rewrite `zBox` as an `Icc`.
  simpa [zBox_eq_Icc (td := td)] using innerSumUZ_eq_sum_zBox (td := td) (ξ := ξ) (F := F) (u := u)

theorem sum_zBox_eq_sum_range {α : Type*} [AddCommMonoid α] (td : TubeData) (f : ℤ → α) :
    (∑ z ∈ IndexBounds.zBox td, f z)
      =
    ∑ n ∈ Finset.range (zBoxN td), f (zBoxA td + 1 + n) := by
  classical
  simpa [IndexBounds.zBox, zBoxA, zBoxB, zBoxN, sum_Ioc_eq_sum_range] using
    (sum_Ioc_eq_sum_range (a := zBoxA td) (b := zBoxB td) (f := f))

def zBoxVA (td : TubeData) : ℤ :=
  (⌊((-td.U - (td.q : ℝ)) / (td.q : ℝ))⌋ : ℤ)

def zBoxVB (td : TubeData) : ℤ :=
  (⌈(td.U) / (td.q : ℝ)⌉ : ℤ)

def zBoxVN (td : TubeData) : ℕ :=
  (zBoxVB td + 1 - zBoxVA td).toNat

theorem zBoxV_eq_Icc (td : TubeData) :
    IndexBounds.zBoxV td = Finset.Icc (zBoxVA td) (zBoxVB td) := by
  rfl

/-- Step 4: rewrite `innerSumVZ` as a sum over the explicit interval `Icc zBoxVA zBoxVB`. -/
theorem innerSumVZ_eq_sum_Icc_zBoxV (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (v : ℤ) :
    innerSumVZ td ξ F v
      =
    ∑ z ∈ Finset.Icc (zBoxVA td) (zBoxVB td),
      (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
  simpa [zBoxV_eq_Icc (td := td)] using innerSumVZ_eq_sum_zBoxV (td := td) (ξ := ξ) (F := F) (v := v)

theorem sum_zBoxV_eq_sum_range {α : Type*} [AddCommMonoid α] (td : TubeData) (f : ℤ → α) :
    (∑ z ∈ IndexBounds.zBoxV td, f z)
      =
    ∑ n ∈ Finset.range (zBoxVN td), f (zBoxVA td + n) := by
  classical
  simpa [IndexBounds.zBoxV, zBoxVA, zBoxVB, zBoxVN, sum_Icc_eq_sum_range] using
    (sum_Icc_eq_sum_range (a := zBoxVA td) (b := zBoxVB td) (f := f))

/-!
## Phase factoring for translated boxes

These lemmas are pure algebra: they rewrite the uniform `z`-sums as translated `range` sums and
factor out the constant “base-point phase” `e(ξ*u*z₀/X)` or `e(ξ*v*z₀/X)`.

They are useful because:
* they remove the dependence on the absolute `z`-location (only the translated index `n` remains);
* the factored phase is unimodular, so it disappears in `‖·‖` and `‖·‖^2` bounds.
-/

/-- Step 3: `innerSumUZ` as a translated `range` sum, with the base-point phase factored out. -/
theorem innerSumUZ_eq_phase_mul_sum_range (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (u : ℤ) :
    innerSumUZ td ξ F u
      =
    (e (ξ * (u : ℝ) * ((zBoxA td + 1 : ℤ) : ℝ) / td.X)) *
      (∑ n ∈ Finset.range (zBoxN td),
        (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
          e (ξ * (u : ℝ) * (n : ℝ) / td.X)) := by
  classical
  -- First rewrite the `z`-sum to the uniform box and then to a translated `range` sum.
  have hzbox :
      innerSumUZ td ξ F u
        =
      ∑ n ∈ Finset.range (zBoxN td),
        (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
          e (ξ * (u : ℝ) * ((zBoxA td + 1 + n : ℤ) : ℝ) / td.X) := by
    -- `innerSumUZ` → `zBox` → `range`.
    calc
      innerSumUZ td ξ F u
          =
        ∑ z ∈ IndexBounds.zBox td,
          (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) :=
            innerSumUZ_eq_sum_zBox (td := td) (ξ := ξ) (F := F) (u := u)
      _ =
        ∑ n ∈ Finset.range (zBoxN td),
          (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
            e (ξ * (u : ℝ) * ((zBoxA td + 1 + n : ℤ) : ℝ) / td.X) := by
          -- Apply `sum_zBox_eq_sum_range` with `f z := (...) * e(...)`.
          simpa using
            (sum_zBox_eq_sum_range (td := td)
              (f := fun z : ℤ =>
                (∑ p ∈ fiberUZ td u z, F p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X)))
  -- Now factor the constant phase `e(ξ*u*(z0)/X)` out of the `range` sum.
  -- Use `e(x+y)=e x * e y` with `z = z0 + n`.
  have hphase (n : ℕ) :
      e (ξ * (u : ℝ) * ((zBoxA td + 1 + n : ℤ) : ℝ) / td.X)
        =
      e (ξ * (u : ℝ) * ((zBoxA td + 1 : ℤ) : ℝ) / td.X) *
        e (ξ * (u : ℝ) * (n : ℝ) / td.X) := by
    let x : ℝ := ξ * (u : ℝ) * ((zBoxA td + 1 : ℤ) : ℝ) / td.X
    let y : ℝ := ξ * (u : ℝ) * (n : ℝ) / td.X
    have hsplit :
        ξ * (u : ℝ) * ((zBoxA td + 1 + n : ℤ) : ℝ) / td.X = x + y := by
      simp [x, y, div_eq_mul_inv, mul_add, add_mul, add_assoc, mul_assoc, mul_left_comm, mul_comm]
    calc
      e (ξ * (u : ℝ) * ((zBoxA td + 1 + n : ℤ) : ℝ) / td.X)
          = e (x + y) := by
              -- Avoid `simp` normal-form changes; use direct congruence.
              simpa using congrArg e hsplit
      _ = e x * e y := e_add x y
      _ = e (ξ * (u : ℝ) * ((zBoxA td + 1 : ℤ) : ℝ) / td.X) *
            e (ξ * (u : ℝ) * (n : ℝ) / td.X) := by
            simp [x, y]
  -- Rewrite each summand using `hphase`, then factor out the constant phase.
  -- (We keep the coefficient sum in front, to avoid rewriting it.)
  calc
    innerSumUZ td ξ F u
        = ∑ n ∈ Finset.range (zBoxN td),
            (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
              e (ξ * (u : ℝ) * ((zBoxA td + 1 + n : ℤ) : ℝ) / td.X) := hzbox
    _ = ∑ n ∈ Finset.range (zBoxN td),
          (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
            (e (ξ * (u : ℝ) * ((zBoxA td + 1 : ℤ) : ℝ) / td.X) *
              e (ξ * (u : ℝ) * (n : ℝ) / td.X)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          -- Direct rewrite of the exponential factor (avoid `simp` rewriting `a*b = a*c`).
          rw [hphase n]
    _ =
        e (ξ * (u : ℝ) * ((zBoxA td + 1 : ℤ) : ℝ) / td.X) *
          (∑ n ∈ Finset.range (zBoxN td),
            (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
              e (ξ * (u : ℝ) * (n : ℝ) / td.X)) := by
          -- Factor the constant out.
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Step 3: the factored base-point phase in `innerSumUZ_eq_phase_mul_sum_range` disappears in norm. -/
theorem norm_innerSumUZ_eq_norm_sum_range (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (u : ℤ) :
    ‖innerSumUZ td ξ F u‖
      =
    ‖∑ n ∈ Finset.range (zBoxN td),
        (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
          e (ξ * (u : ℝ) * (n : ℝ) / td.X)‖ := by
  classical
  -- Use the phase factoring lemma and `‖e(·)‖ = 1`.
  let s : ℂ :=
    ∑ n ∈ Finset.range (zBoxN td),
      (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
        e (ξ * (u : ℝ) * (n : ℝ) / td.X)
  have h :=
    innerSumUZ_eq_phase_mul_sum_range (td := td) (ξ := ξ) (F := F) (u := u)
  -- `innerSumUZ = phase * s`.
  have h' :
      innerSumUZ td ξ F u
        =
      (e (ξ * (u : ℝ) * ((zBoxA td + 1 : ℤ) : ℝ) / td.X)) * s := by
    simpa [s] using h
  -- Take norms and simplify.
  calc
    ‖innerSumUZ td ξ F u‖ = ‖(e (ξ * (u : ℝ) * ((zBoxA td + 1 : ℤ) : ℝ) / td.X)) * s‖ := by
        simpa [h']
    _ = ‖e (ξ * (u : ℝ) * ((zBoxA td + 1 : ℤ) : ℝ) / td.X)‖ * ‖s‖ := by
        simp [norm_mul]
    _ = ‖s‖ := by simp [norm_e]
    _ = ‖∑ n ∈ Finset.range (zBoxN td),
          (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
            e (ξ * (u : ℝ) * (n : ℝ) / td.X)‖ := by
        simp [s]

/-- Step 4: `innerSumVZ` as a translated `range` sum, with the base-point phase factored out. -/
theorem innerSumVZ_eq_phase_mul_sum_range (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (v : ℤ) :
    innerSumVZ td ξ F v
      =
    (e (ξ * ((zBoxVA td : ℤ) : ℝ) * (v : ℝ) / td.X)) *
      (∑ n ∈ Finset.range (zBoxVN td),
        (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
          e (ξ * (n : ℝ) * (v : ℝ) / td.X)) := by
  classical
  have hzbox :
      innerSumVZ td ξ F v
        =
      ∑ n ∈ Finset.range (zBoxVN td),
        (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
          e (ξ * ((zBoxVA td + n : ℤ) : ℝ) * (v : ℝ) / td.X) := by
    calc
      innerSumVZ td ξ F v
          =
        ∑ z ∈ IndexBounds.zBoxV td,
          (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) :=
            innerSumVZ_eq_sum_zBoxV (td := td) (ξ := ξ) (F := F) (v := v)
      _ =
        ∑ n ∈ Finset.range (zBoxVN td),
          (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
            e (ξ * ((zBoxVA td + n : ℤ) : ℝ) * (v : ℝ) / td.X) := by
          simpa using
            (sum_zBoxV_eq_sum_range (td := td)
              (f := fun z : ℤ =>
                (∑ p ∈ fiberVZ td v z, F p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X)))
  have hphase (n : ℕ) :
      e (ξ * ((zBoxVA td + n : ℤ) : ℝ) * (v : ℝ) / td.X)
        =
      e (ξ * ((zBoxVA td : ℤ) : ℝ) * (v : ℝ) / td.X) *
        e (ξ * (n : ℝ) * (v : ℝ) / td.X) := by
    -- Split `(z0 + n)` into `z0` and `n`.
    let x : ℝ := ξ * ((zBoxVA td : ℤ) : ℝ) * (v : ℝ) / td.X
    let y : ℝ := ξ * (n : ℝ) * (v : ℝ) / td.X
    have hsplit :
        ξ * ((zBoxVA td + n : ℤ) : ℝ) * (v : ℝ) / td.X = x + y := by
      -- purely commutative ring arithmetic in `ℝ`
      simp [x, y, div_eq_mul_inv, mul_add, add_mul, add_assoc, mul_assoc, mul_left_comm, mul_comm]
    calc
      e (ξ * ((zBoxVA td + n : ℤ) : ℝ) * (v : ℝ) / td.X)
          = e (x + y) := by
              simpa using congrArg e hsplit
      _ = e x * e y := e_add x y
      _ = e (ξ * ((zBoxVA td : ℤ) : ℝ) * (v : ℝ) / td.X) *
            e (ξ * (n : ℝ) * (v : ℝ) / td.X) := by
            simp [x, y]
  calc
    innerSumVZ td ξ F v
        = ∑ n ∈ Finset.range (zBoxVN td),
            (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
              e (ξ * ((zBoxVA td + n : ℤ) : ℝ) * (v : ℝ) / td.X) := hzbox
    _ = ∑ n ∈ Finset.range (zBoxVN td),
          (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
            (e (ξ * ((zBoxVA td : ℤ) : ℝ) * (v : ℝ) / td.X) *
              e (ξ * (n : ℝ) * (v : ℝ) / td.X)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [hphase n]
    _ =
        e (ξ * ((zBoxVA td : ℤ) : ℝ) * (v : ℝ) / td.X) *
          (∑ n ∈ Finset.range (zBoxVN td),
            (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
              e (ξ * (n : ℝ) * (v : ℝ) / td.X)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Step 4: the factored base-point phase in `innerSumVZ_eq_phase_mul_sum_range` disappears in norm. -/
theorem norm_innerSumVZ_eq_norm_sum_range (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (v : ℤ) :
    ‖innerSumVZ td ξ F v‖
      =
    ‖∑ n ∈ Finset.range (zBoxVN td),
        (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
          e (ξ * (n : ℝ) * (v : ℝ) / td.X)‖ := by
  classical
  let s : ℂ :=
    ∑ n ∈ Finset.range (zBoxVN td),
      (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
        e (ξ * (n : ℝ) * (v : ℝ) / td.X)
  have h :=
    innerSumVZ_eq_phase_mul_sum_range (td := td) (ξ := ξ) (F := F) (v := v)
  have h' :
      innerSumVZ td ξ F v
        =
      (e (ξ * ((zBoxVA td : ℤ) : ℝ) * (v : ℝ) / td.X)) * s := by
    simpa [s] using h
  calc
    ‖innerSumVZ td ξ F v‖ =
        ‖(e (ξ * ((zBoxVA td : ℤ) : ℝ) * (v : ℝ) / td.X)) * s‖ := by
          simpa [h']
    _ = ‖e (ξ * ((zBoxVA td : ℤ) : ℝ) * (v : ℝ) / td.X)‖ * ‖s‖ := by
          simp [norm_mul]
    _ = ‖s‖ := by simp [norm_e]
    _ = ‖∑ n ∈ Finset.range (zBoxVN td),
          (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
            e (ξ * (n : ℝ) * (v : ℝ) / td.X)‖ := by
          simp [s]

end ZBoxRewrite

end

end LargeSieve
end TypeII
end Engines
end SSU
