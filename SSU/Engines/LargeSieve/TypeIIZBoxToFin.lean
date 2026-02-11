import SSU.Engines.LargeSieve.TypeIIZBoxRewrite
import Mathlib.Data.Fin.Basic

/-!
Deterministic `range` → `Fin N` reindexing helpers for TeX Step 3/4.

After rewriting `innerSumUZ` / `innerSumVZ` as translated `range` sums over the uniform boxes
`zBox td` / `zBoxV td`, we often want to apply the MV engine which is packaged on `Fin N`.

This file contains only index plumbing:
* define the `Fin`-indexed coefficient arrays corresponding to the translated `range` sums;
* rewrite `∑ n ∈ range N, ...` as `∑ k ∈ (univ : Finset (Fin N)), ...`.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace ZBoxToFin

open SSU.Engines.TypeII
open ZBoxRewrite

/-!
## Step 3 (`u`-fibers): coefficients on `Fin (zBoxN td)`
-/

/-- Step 3 coefficient array for the translated `zBox td` range sum (depends on `u`). -/
def coeffUZFin (td : TubeData) (F : TubePoint → ℂ) (u : ℤ) : Fin (zBoxN td) → ℂ :=
  fun k => ∑ p ∈ fiberUZ td u (zBoxA td + 1 + (k : ℕ)), F p

theorem sum_range_eq_sum_univ_coeffUZFin
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (u : ℤ) :
    (∑ n ∈ Finset.range (zBoxN td),
        (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
          e (ξ * (u : ℝ) * (n : ℝ) / td.X))
      =
    ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
      (coeffUZFin td F u k) *
        e (ξ * (u : ℝ) * ((k : ℕ) : ℝ) / td.X) := by
  classical
  -- Convert the `Finset.univ` sum to a `Fin` sum, then to a `range` sum.
  -- Finally unfold `coeffUZFin`.
  -- `Finset.sum_fin_eq_sum_range` is the key rewrite for `Fin`.
  calc
    (∑ n ∈ Finset.range (zBoxN td),
        (∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p) *
          e (ξ * (u : ℝ) * (n : ℝ) / td.X))
        =
      ∑ k : Fin (zBoxN td),
        (∑ p ∈ fiberUZ td u (zBoxA td + 1 + (k : ℕ)), F p) *
          e (ξ * (u : ℝ) * ((k : ℕ) : ℝ) / td.X) := by
          -- Rewrite `∑ k : Fin N` as `∑ n ∈ range N` (eliminating the `if` using `n < N`).
          symm
          let g : Fin (zBoxN td) → ℂ :=
            fun k =>
              (∑ p ∈ fiberUZ td u (zBoxA td + 1 + (k : ℕ)), F p) *
                e (ξ * (u : ℝ) * ((k : ℕ) : ℝ) / td.X)
          have h0 := (Finset.sum_fin_eq_sum_range (n := zBoxN td) (c := g))
          -- `sum_fin_eq_sum_range` produces an `if x < N` term; simplify it on `x ∈ range N`.
          have h1 :
              (∑ k : Fin (zBoxN td), g k)
                =
              ∑ x ∈ Finset.range (zBoxN td),
                (∑ p ∈ fiberUZ td u (zBoxA td + 1 + x), F p) *
                  e (ξ * (u : ℝ) * (x : ℝ) / td.X) := by
            refine h0.trans ?_
            classical
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hxlt : x < zBoxN td := (Finset.mem_range.1 hx)
            -- `if hxlt then g ⟨x,hxlt⟩ else 0` simplifies to the displayed summand.
            simp [g, hxlt]
          simpa [g] using h1
    _ = ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
        (∑ p ∈ fiberUZ td u (zBoxA td + 1 + (k : ℕ)), F p) *
          e (ξ * (u : ℝ) * ((k : ℕ) : ℝ) / td.X) := by
          simp
    _ = ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
        (coeffUZFin td F u k) *
          e (ξ * (u : ℝ) * ((k : ℕ) : ℝ) / td.X) := by
          simp [coeffUZFin]

/-- Step 3: `‖innerSumUZ‖` equals the norm of the corresponding `Fin`-indexed exponential sum. -/
theorem norm_innerSumUZ_eq_norm_sum_univ_coeffUZFin
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (u : ℤ) :
    ‖innerSumUZ td ξ F u‖
      =
    ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
        (coeffUZFin td F u k) *
          e (ξ * (u : ℝ) * ((k : ℕ) : ℝ) / td.X)‖ := by
  classical
  -- Start from the phase-factored range form and rewrite to `Fin`.
  -- (The base-point phase drops in the norm.)
  have h0 :=
    ZBoxRewrite.norm_innerSumUZ_eq_norm_sum_range (td := td) (ξ := ξ) (F := F) (u := u)
  -- Rewrite the `range` sum as a `Fin` sum.
  have h1 :=
    sum_range_eq_sum_univ_coeffUZFin (td := td) (ξ := ξ) (F := F) (u := u)
  -- Combine.
  -- `h0` is equality of norms; rewrite its RHS using `h1`.
  -- `simp` handles the rewriting inside the norm.
  simpa [h1] using h0

/-- Step 3 (residue + progression parameter form): specialize the `Fin`-indexed exponential sum to
`u = uResidue(r) + m*q` (i.e. `uFromIndex r m`) and split the phase accordingly.

This is deterministic TeX bookkeeping: it prepares the `m`-sum for an MV-on-a-progression lemma. -/
theorem norm_innerSumUZ_uFromIndex_eq_norm_sum_univ_phaseSplit
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (r m : ℤ) :
    ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖
      =
    ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
        (coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m) k) *
          e (ξ * (uResidue td r : ℝ) * ((k : ℕ) : ℝ) / td.X) *
          e (ξ * ((m : ℝ) * (td.q : ℝ)) * ((k : ℕ) : ℝ) / td.X)‖ := by
  classical
  -- Start from the `u`-version, then rewrite the phase using `uFromIndex`.
  have h0 :=
    norm_innerSumUZ_eq_norm_sum_univ_coeffUZFin (td := td) (ξ := ξ) (F := F)
      (u := ResiduePartition.uFromIndex (td := td) r m)
  -- Rewrite each summand's phase pointwise.
  refine h0.trans ?_
  refine congrArg (fun z : ℂ => ‖z‖) ?_
  refine Finset.sum_congr rfl ?_
  intro k hk
  -- `uFromIndex r m = uResidue r + m*q`.
  have huR : ((ResiduePartition.uFromIndex (td := td) r m : ℤ) : ℝ)
      = (uResidue td r : ℝ) + (m : ℝ) * (td.q : ℝ) := by
    simp [ResiduePartition.uFromIndex, Int.cast_add, Int.cast_mul]
  have e_add (x y : ℝ) : e (x + y) = e x * e y := by
    simp [TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  have hsplit :
      ξ * ((ResiduePartition.uFromIndex (td := td) r m : ℤ) : ℝ) * ((k : ℕ) : ℝ) / td.X
        =
      (ξ * (uResidue td r : ℝ) * ((k : ℕ) : ℝ) / td.X) +
      (ξ * ((m : ℝ) * (td.q : ℝ)) * ((k : ℕ) : ℝ) / td.X) := by
    simp [huR, div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm]
  have heSplit :
      e (ξ * ((ResiduePartition.uFromIndex (td := td) r m : ℤ) : ℝ) * ((k : ℕ) : ℝ) / td.X)
        =
      e (ξ * (uResidue td r : ℝ) * ((k : ℕ) : ℝ) / td.X) *
        e (ξ * ((m : ℝ) * (td.q : ℝ)) * ((k : ℕ) : ℝ) / td.X) := by
    have h0' := congrArg e hsplit
    exact h0'.trans (by simpa using (e_add _ _))
  -- Apply the additive rule for `e` and reassociate.
  calc
    (coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m) k) *
        e (ξ * ((ResiduePartition.uFromIndex (td := td) r m : ℤ) : ℝ) * ((k : ℕ) : ℝ) / td.X)
        =
      (coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m) k) *
        (e (ξ * (uResidue td r : ℝ) * ((k : ℕ) : ℝ) / td.X) *
          e (ξ * ((m : ℝ) * (td.q : ℝ)) * ((k : ℕ) : ℝ) / td.X)) := by
          simpa [heSplit]
    _ =
      (coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m) k) *
        e (ξ * (uResidue td r : ℝ) * ((k : ℕ) : ℝ) / td.X) *
          e (ξ * ((m : ℝ) * (td.q : ℝ)) * ((k : ℕ) : ℝ) / td.X) := by
          ring

/-!
## Step 4 (`v`-fibers): coefficients on `Fin (zBoxVN td)`
-/

/-- Step 4 coefficient array for the translated `zBoxV td` range sum (depends on `v`). -/
def coeffVZFin (td : TubeData) (F : TubePoint → ℂ) (v : ℤ) : Fin (zBoxVN td) → ℂ :=
  fun k => ∑ p ∈ fiberVZ td v (zBoxVA td + (k : ℕ)), F p

theorem sum_range_eq_sum_univ_coeffVZFin
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (v : ℤ) :
    (∑ n ∈ Finset.range (zBoxVN td),
        (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
          e (ξ * (n : ℝ) * (v : ℝ) / td.X))
      =
    ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
      (coeffVZFin td F v k) *
        e (ξ * ((k : ℕ) : ℝ) * (v : ℝ) / td.X) := by
  classical
  calc
    (∑ n ∈ Finset.range (zBoxVN td),
        (∑ p ∈ fiberVZ td v (zBoxVA td + n), F p) *
          e (ξ * (n : ℝ) * (v : ℝ) / td.X))
        =
      ∑ k : Fin (zBoxVN td),
        (∑ p ∈ fiberVZ td v (zBoxVA td + (k : ℕ)), F p) *
          e (ξ * ((k : ℕ) : ℝ) * (v : ℝ) / td.X) := by
          symm
          let g : Fin (zBoxVN td) → ℂ :=
            fun k =>
              (∑ p ∈ fiberVZ td v (zBoxVA td + (k : ℕ)), F p) *
                e (ξ * ((k : ℕ) : ℝ) * (v : ℝ) / td.X)
          have h0 := (Finset.sum_fin_eq_sum_range (n := zBoxVN td) (c := g))
          have h1 :
              (∑ k : Fin (zBoxVN td), g k)
                =
              ∑ x ∈ Finset.range (zBoxVN td),
                (∑ p ∈ fiberVZ td v (zBoxVA td + x), F p) *
                  e (ξ * (x : ℝ) * (v : ℝ) / td.X) := by
            refine h0.trans ?_
            classical
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hxlt : x < zBoxVN td := (Finset.mem_range.1 hx)
            simp [g, hxlt]
          simpa [g] using h1
    _ = ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
        (∑ p ∈ fiberVZ td v (zBoxVA td + (k : ℕ)), F p) *
          e (ξ * ((k : ℕ) : ℝ) * (v : ℝ) / td.X) := by
          simp
    _ = ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
        (coeffVZFin td F v k) *
          e (ξ * ((k : ℕ) : ℝ) * (v : ℝ) / td.X) := by
          simp [coeffVZFin]

/-- Step 4: `‖innerSumVZ‖` equals the norm of the corresponding `Fin`-indexed exponential sum. -/
theorem norm_innerSumVZ_eq_norm_sum_univ_coeffVZFin
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (v : ℤ) :
    ‖innerSumVZ td ξ F v‖
      =
    ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
        (coeffVZFin td F v k) *
          e (ξ * ((k : ℕ) : ℝ) * (v : ℝ) / td.X)‖ := by
  classical
  have h0 :=
    ZBoxRewrite.norm_innerSumVZ_eq_norm_sum_range (td := td) (ξ := ξ) (F := F) (v := v)
  have h1 :=
    sum_range_eq_sum_univ_coeffVZFin (td := td) (ξ := ξ) (F := F) (v := v)
  simpa [h1] using h0

/-- Step 4 (residue + progression parameter form): specialize to `v = vResidue(r) + m*q`
(`vFromIndex r m`) and split the phase accordingly. -/
theorem norm_innerSumVZ_vFromIndex_eq_norm_sum_univ_phaseSplit
    (td : TubeData) (ξ : ℝ) (F : TubePoint → ℂ) (r m : ℤ) :
    ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖
      =
    ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
        (coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m) k) *
          e (ξ * ((k : ℕ) : ℝ) * (vResidue td r : ℝ) / td.X) *
          e (ξ * ((k : ℕ) : ℝ) * ((m : ℝ) * (td.q : ℝ)) / td.X)‖ := by
  classical
  have h0 :=
    norm_innerSumVZ_eq_norm_sum_univ_coeffVZFin (td := td) (ξ := ξ) (F := F)
      (v := ResiduePartitionV.vFromIndex (td := td) r m)
  refine h0.trans ?_
  refine congrArg (fun z : ℂ => ‖z‖) ?_
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hvR : ((ResiduePartitionV.vFromIndex (td := td) r m : ℤ) : ℝ)
      = (vResidue td r : ℝ) + (m : ℝ) * (td.q : ℝ) := by
    simp [ResiduePartitionV.vFromIndex, Int.cast_add, Int.cast_mul]
  have e_add (x y : ℝ) : e (x + y) = e x * e y := by
    simp [TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  have hsplit :
      ξ * ((k : ℕ) : ℝ) * ((ResiduePartitionV.vFromIndex (td := td) r m : ℤ) : ℝ) / td.X
        =
      (ξ * ((k : ℕ) : ℝ) * (vResidue td r : ℝ) / td.X) +
      (ξ * ((k : ℕ) : ℝ) * ((m : ℝ) * (td.q : ℝ)) / td.X) := by
    simp [hvR, div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm]
  have heSplit :
      e (ξ * ((k : ℕ) : ℝ) * ((ResiduePartitionV.vFromIndex (td := td) r m : ℤ) : ℝ) / td.X)
        =
      e (ξ * ((k : ℕ) : ℝ) * (vResidue td r : ℝ) / td.X) *
        e (ξ * ((k : ℕ) : ℝ) * ((m : ℝ) * (td.q : ℝ)) / td.X) := by
    have h0' := congrArg e hsplit
    -- `hsplit` expresses the phase as a sum; now split the exponential.
    exact h0'.trans (by simpa using (e_add _ _))
  calc
    (coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m) k) *
        e (ξ * ((k : ℕ) : ℝ) * ((ResiduePartitionV.vFromIndex (td := td) r m : ℤ) : ℝ) / td.X)
        =
      (coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m) k) *
        (e (ξ * ((k : ℕ) : ℝ) * (vResidue td r : ℝ) / td.X) *
          e (ξ * ((k : ℕ) : ℝ) * ((m : ℝ) * (td.q : ℝ)) / td.X)) := by
          simpa [heSplit]
    _ =
      (coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m) k) *
        e (ξ * ((k : ℕ) : ℝ) * (vResidue td r : ℝ) / td.X) *
          e (ξ * ((k : ℕ) : ℝ) * ((m : ℝ) * (td.q : ℝ)) / td.X) := by
          ring

end ZBoxToFin

end
end LargeSieve
end TypeII
end Engines
end SSU
