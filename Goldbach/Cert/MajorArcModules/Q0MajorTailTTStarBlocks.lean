import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Deterministic scaffolding for ε₂-large TT*/Toeplitz “successive approximation”.

This file provides two generic, certificate-friendly tools:

1. **Blockwise Cauchy–Schwarz** for finite sums:
   `‖∑_b z_b‖^2 ≤ (#blocks) * ∑_b ‖z_b‖^2`,
   and its version after summing over a second finite index (`k`).

2. A canonical **dyadic block indexing** for `q ≤ Q0` matching the Python experiment scripts:
   blocks are `(0,1]`, `(1,2]`, `(2,4]`, …, truncated at `Q0`.

No number theory is used here; these lemmas are intended as the first “scaffold” step before any
dispersion/large-sieve technology is introduced.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks

open scoped BigOperators

/-!
## Blockwise Cauchy–Schwarz
-/

theorem norm_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  classical
  -- Triangle inequality, then Cauchy–Schwarz on the real nonnegative sequence `‖z i‖`.
  have htri : ‖∑ i ∈ s, z i‖ ≤ ∑ i ∈ s, ‖z i‖ := by
    simpa using (norm_sum_le (s := s) (f := fun i => z i))
  have hsq : ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 := by
    have h0a : 0 ≤ ‖∑ i ∈ s, z i‖ := norm_nonneg _
    have h0b : 0 ≤ ∑ i ∈ s, ‖z i‖ := by
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    -- Square by multiplying both sides by themselves.
    have : (‖∑ i ∈ s, z i‖) * (‖∑ i ∈ s, z i‖) ≤ (∑ i ∈ s, ‖z i‖) * (∑ i ∈ s, ‖z i‖) :=
      mul_le_mul htri htri h0a h0b
    simpa [pow_two, mul_assoc] using this
  have hcs :
      (∑ i ∈ s, ‖z i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (‖z i‖) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖z i‖))
  exact le_trans hsq hcs

theorem sum_sq_norm_sum_le_card_mul_sum_sum_sq
    {ι κ : Type} (blocks : Finset ι) (ks : Finset κ) (F : ι → κ → ℂ) :
    (∑ k ∈ ks, ‖∑ b ∈ blocks, F b k‖ ^ 2)
      ≤
    (blocks.card : ℝ) * ∑ b ∈ blocks, ∑ k ∈ ks, ‖F b k‖ ^ 2 := by
  classical
  -- Apply the previous lemma pointwise in `k`, then sum over `k`.
  have hk :
      ∀ k ∈ ks,
        ‖∑ b ∈ blocks, F b k‖ ^ 2 ≤ (blocks.card : ℝ) * ∑ b ∈ blocks, ‖F b k‖ ^ 2 := by
    intro k hk
    -- `norm_sum_sq_le_card_mul_sum_norm_sq` is stated for a single `Finset`.
    simpa using
      (norm_sum_sq_le_card_mul_sum_norm_sq (s := blocks) (z := fun b => F b k))
  -- Sum those inequalities over `k ∈ ks`.
  have hsum :
      (∑ k ∈ ks, ‖∑ b ∈ blocks, F b k‖ ^ 2)
        ≤
      ∑ k ∈ ks, (blocks.card : ℝ) * ∑ b ∈ blocks, ‖F b k‖ ^ 2 :=
    Finset.sum_le_sum (fun k hk' => hk k hk')
  -- Pull out the constant `#blocks` and commute the finite sums.
  calc
    (∑ k ∈ ks, ‖∑ b ∈ blocks, F b k‖ ^ 2)
        ≤
      ∑ k ∈ ks, (blocks.card : ℝ) * ∑ b ∈ blocks, ‖F b k‖ ^ 2 := hsum
    _ =
      (blocks.card : ℝ) * ∑ k ∈ ks, ∑ b ∈ blocks, ‖F b k‖ ^ 2 := by
      simp [Finset.mul_sum]
    _ =
      (blocks.card : ℝ) * ∑ b ∈ blocks, ∑ k ∈ ks, ‖F b k‖ ^ 2 := by
      -- Fubini for `Finset.sum`.
      rw [Finset.sum_comm]

/-!
## Dyadic q-block indexing (matching `scripts/experiments/*q_decomposition.py`)
-/

open Nat

/-- Dyadic block index for `q ≥ 1`: `q = 1 ↦ 0`, `q = 2 ↦ 1`, `q ∈ {3,4} ↦ 2`, etc. -/
def dyadicBlockId (q : ℕ) : ℕ :=
  if q = 1 then 0 else Nat.log2 (q - 1) + 1

/-- Number of dyadic blocks needed to cover `{1,…,Q0}` (for `Q0 ≥ 1`). -/
def dyadicBlockCount (Q0 : ℕ) : ℕ :=
  if Q0 ≤ 1 then 1 else Nat.log2 (Q0 - 1) + 2

theorem dyadicBlockId_lt_count {Q0 q : ℕ} (hq : q ∈ Finset.Icc (1 : ℕ) Q0) :
    dyadicBlockId q < dyadicBlockCount Q0 := by
  classical
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hqQ : q ≤ Q0 := (Finset.mem_Icc.mp hq).2
  by_cases hQ0 : Q0 ≤ 1
  · -- In this case `Q0 = 0` or `Q0 = 1`, hence `q = 1`.
    have hq' : q = 1 := by
      have : q ≤ 1 := le_trans hqQ hQ0
      exact le_antisymm this hq1
    simp [dyadicBlockCount, dyadicBlockId, hQ0, hq']
  · -- Now `Q0 ≥ 2`.
    have hQ0' : ¬ Q0 ≤ 1 := hQ0
    by_cases hqEq : q = 1
    · simp [dyadicBlockId, dyadicBlockCount, hQ0, hqEq]
    · -- `q ≥ 2`, so `q - 1 ≤ Q0 - 1` and `log2 (q-1) ≤ log2 (Q0-1)`.
      have hqNe : 1 ≠ q := by simpa [eq_comm] using hqEq
      have hq2 : 2 ≤ q := (Nat.succ_le_iff).2 (lt_of_le_of_ne hq1 hqNe)
      have hsub : q - 1 ≤ Q0 - 1 := Nat.sub_le_sub_right hqQ 1
      have hlog :
          Nat.log2 (q - 1) ≤ Nat.log2 (Q0 - 1) := by
        -- `log2` is `log 2`.
        have : Nat.log 2 (q - 1) ≤ Nat.log 2 (Q0 - 1) := Nat.log_mono_right hsub
        simpa [Nat.log2_eq_log_two] using this
      have : Nat.log2 (q - 1) + 1 < Nat.log2 (Q0 - 1) + 2 := by
        exact Nat.add_lt_add_right (Nat.lt_succ_of_le hlog) 1
      simpa [dyadicBlockId, dyadicBlockCount, hQ0, hqEq, Nat.add_assoc] using this

theorem sum_over_dyadicBlocks_eq
    {α : Type} [AddCommMonoid α] {Q0 : ℕ} (f : ℕ → α) :
    (∑ q ∈ Finset.Icc (1 : ℕ) Q0, f q)
      =
    ∑ j ∈ Finset.range (dyadicBlockCount Q0),
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0, if dyadicBlockId q = j then f q else 0 := by
  classical
  -- Swap the two finite sums and collapse the inner `j`-sum pointwise in `q`.
  symm
  calc
    (∑ j ∈ Finset.range (dyadicBlockCount Q0),
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0, if dyadicBlockId q = j then f q else 0)
        =
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ j ∈ Finset.range (dyadicBlockCount Q0), if dyadicBlockId q = j then f q else 0 := by
          simpa [Finset.sum_comm]
    _ =
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0, f q := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          have hmem :
              dyadicBlockId q ∈ Finset.range (dyadicBlockCount Q0) :=
            Finset.mem_range.mpr (dyadicBlockId_lt_count (Q0 := Q0) (q := q) hq)
          -- `∑ j, if a = j then b else 0 = b` when `a ∈ range`.
          simpa using
            (Finset.sum_ite_eq_of_mem (s := Finset.range (dyadicBlockCount Q0))
              (a := dyadicBlockId q) (b := fun _ : ℕ => f q) hmem)

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks
