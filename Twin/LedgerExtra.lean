/-
  Twin/LedgerExtra.lean
  ---------------------
  Extra lemmas used across the Twin pipeline.
  Import hygiene:
    • DO NOT import Twin.Compat here (avoids cycle).
    • DO NOT import this file itself.
-/

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Twin.GoalAPI
import Twin.Ledger   -- adjust if your windowSum core lives elsewhere

namespace Twin
namespace LedgerExtra

open Real
open scoped BigOperators

/-- Windowed Cauchy–Schwarz on `[X, X+H]`.
    Standard ℓ¹/ℓ² control with span `(H+1)`. -/
lemma window_l1_le_sqrt_span_mul_window_l2
    (X H : ℕ) (e : ℕ → ℝ) :
    Ledger.windowSum X H (fun n => |e n|)
      ≤ Real.sqrt ((↑H : ℝ) + 1) *
        Real.sqrt (Ledger.windowSum X H (fun n => e n ^ 2)) := by
  classical
  set s := Finset.range (H + 1)
  -- convenient shorthands for the two windowed sums
  set A := Ledger.windowSum X H (fun n => |e n|)
  set L2 := Ledger.windowSum X H (fun n => e n ^ 2)
  have hA_sum : A = ∑ k in s, |e (X + k)| := by
    simp [A, Ledger.windowSum, Ledger.windowSumN, s]
  have hL2_sum : L2 = ∑ k in s, e (X + k) ^ 2 := by
    simp [L2, Ledger.windowSum, Ledger.windowSumN, s]
  have hs_card : (s.card : ℝ) = (H : ℝ) + 1 := by
    simp [s, Nat.cast_add, Nat.cast_one]
  have hN_nonneg : 0 ≤ (H : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (H : ℝ) := by exact_mod_cast Nat.zero_le H
    exact add_nonneg this zero_le_one
  have hA_nonneg : 0 ≤ A := by
    have : ∀ k ∈ s, 0 ≤ |e (X + k)| := by
      intro k _; exact abs_nonneg _
    simpa [A, Ledger.windowSum, Ledger.windowSumN, s] using Finset.sum_nonneg this
  have hL2_nonneg : 0 ≤ L2 := by
    have : ∀ k ∈ s, 0 ≤ e (X + k) ^ 2 := by
      intro k _; exact sq_nonneg _
    simpa [L2, Ledger.windowSum, Ledger.windowSumN, s] using Finset.sum_nonneg this
  -- Cauchy–Schwarz in squared form: (∑ |e|)^2 ≤ (H+1) * ∑ |e|^2
  have h_sq :
      A ^ 2 ≤ ((H : ℝ) + 1) * L2 := by
    have hcs :=
      (sq_sum_le_card_mul_sum_sq
          (s := s) (f := fun k : ℕ => |e (X + k)|) :
        (∑ k in s, |e (X + k)|) ^ 2
          ≤ (s.card : ℝ) * ∑ k in s, |e (X + k)| ^ 2)
    have habs_sq :
        ∑ k in s, |e (X + k)| ^ 2 = ∑ k in s, e (X + k) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro k _; simp [pow_two, abs_mul_self]
    simpa [hA_sum, hL2_sum, hs_card, habs_sq] using hcs
  -- turn the squared inequality into the desired square-root form
  have hB_nonneg :
      0 ≤ Real.sqrt ((H : ℝ) + 1) * Real.sqrt L2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hA_le_abs :
      |A| ≤ |Real.sqrt ((H : ℝ) + 1) * Real.sqrt L2| := by
    have h_goal :
        A ^ 2
          ≤ (Real.sqrt ((H : ℝ) + 1) * Real.sqrt L2) ^ 2 := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc,
             Real.mul_self_sqrt hN_nonneg, Real.mul_self_sqrt hL2_nonneg]
        using h_sq
    exact (sq_le_sq).1 h_goal
  simpa [A, Real.abs_of_nonneg hA_nonneg, Real.abs_of_nonneg hB_nonneg]
    using hA_le_abs

/-- For `H : ℕ`, `√(H+1) * √((H+1)/9) = (H+1)/3` in `ℝ`. -/
lemma sqrt_span_mul_sqrt_span_div9 (H : ℕ) :
    sqrt ((↑H : ℝ) + 1) * sqrt (((↑H : ℝ) + 1) / 9)
      = ((↑H : ℝ) + 1) / 3 := by
  set a : ℝ := (↑H : ℝ) + 1
  have ha : 0 ≤ a := by
    have : (0 : ℝ) ≤ (↑H : ℝ) := by exact_mod_cast Nat.zero_le H
    exact add_nonneg this (by norm_num)
  have hα : 0 ≤ a / 9 := div_nonneg ha (by norm_num : (0 : ℝ) ≤ 9)

  -- First: √(a/9) = √a / 3  (no division by √9 anywhere)
 -- First: √(a/9) = √a / 3  (no division by √9, no nested `trans`)
  have h1 : sqrt (a / 9) = sqrt (a * (1 / 9)) := by
    simpa [div_eq_mul_inv]
  have h1over9_nonneg : 0 ≤ (1 / (9 : ℝ)) :=
    (one_div_pos.mpr (by norm_num : 0 < (9 : ℝ))).le
  have h2 : sqrt (a * (1 / 9)) = sqrt a * sqrt (1 / 9) := by
    simpa using Real.sqrt_mul ha h1over9_nonneg
  have h3 : sqrt (1 / 9 : ℝ) = 1 / 3 := by
    have h9nonneg : 0 ≤ (9 : ℝ) := by norm_num
    have : sqrt (9 : ℝ) = 3 := by norm_num
    -- sqrt(1/9) = 1 / sqrt 9 = 1/3
    simpa [one_div, this] using Real.sqrt_inv (x := (9 : ℝ)) h9nonneg
  have h4 : sqrt a * sqrt (1 / 9) = sqrt a / 3 := by
    -- rewrite using h3, then turn (· * (1/3)) into (/ 3)
    rw [h3, one_div, div_eq_mul_inv]
  have h_sqrt_div : sqrt (a / 9) = sqrt a / 3 := by
    -- combine h1 ⟶ h2, then rewrite RHS via h4
    have h01 := h1.trans h2
    rw [h4] at h01; exact h01


  -- Then: √a * √(a/9) = (√a * √a) * (1/3) = a/3
  have hmul : sqrt a * sqrt a = a := Real.mul_self_sqrt ha
  calc
    sqrt a * sqrt (a / 9)
        = sqrt a * (sqrt a / 3) := by simpa [h_sqrt_div]
    _   = (sqrt a * sqrt a) * (1 / 3) := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _   = a * (1 / 3) := by simpa [hmul]
    _   = a / 3 := by simpa [one_div, div_eq_mul_inv]
    _   = ((↑H : ℝ) + 1) / 3 := rfl

/-- Additivity of windowed sums for real-valued functions. -/
lemma windowSum_add (X H : ℕ) (f g : ℕ → ℝ) :
  Ledger.windowSum X H (fun n => f n + g n)
    = Ledger.windowSum X H f + Ledger.windowSum X H g := by
  classical
  unfold Ledger.windowSum
  simpa using
    (Ledger.windowSumN_add (X := X) (N := H + 1) f g)

/-- Windowed sum of a constant function. -/
lemma windowSum_const (X H : ℕ) (c : ℝ) :
  Ledger.windowSum X H (fun _ => c) = ((↑H : ℝ) + 1) * c := by
  classical
  unfold Ledger.windowSum Ledger.windowSumN
  have hsum :
      (Finset.range (H + 1)).sum (fun _ => c) = (H + 1) • c := by
    simpa using Finset.sum_const (c := c) (Finset.range (H + 1))
  simp [hsum, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm,
        add_assoc]


end LedgerExtra
end Twin
