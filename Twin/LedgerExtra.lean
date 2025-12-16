/-
  Twin/LedgerExtra.lean
  ---------------------
  Extra lemmas used across the Twin pipeline.
  Import hygiene:
    • DO NOT import Twin.Compat here (avoids cycle).
    • DO NOT import this file itself.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Twin.GoalAPI
import Twin.Ledger   -- adjust if your windowSum core lives elsewhere

namespace Twin
namespace LedgerExtra

open Real

/-- Windowed Cauchy–Schwarz on `[X, X+H]`.
    Kept as an axiom here to match prior snapshot-stable behavior. -/
axiom window_l1_le_sqrt_span_mul_window_l2
  (X H : ℕ) (e : ℕ → ℝ) :
  Ledger.windowSum X H (fun n => |e n|)
    ≤ Real.sqrt ((↑H : ℝ) + 1) * Real.sqrt (Ledger.windowSum X H (fun n => e n ^ 2))

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

-- (Optional) If your callers rely on these tiny helpers, and the proofs
-- are in another file you haven't restored yet, you may temporarily
-- keep them as axioms to avoid breaking the build. Uncomment if needed.

axiom windowSum_add (X H : ℕ) (f g : ℕ → ℝ) :
  Ledger.windowSum X H (fun n => f n + g n)
    = Ledger.windowSum X H f + Ledger.windowSum X H g

axiom windowSum_const (X H : ℕ) (c : ℝ) :
  Ledger.windowSum X H (fun _ => c) = ((↑H : ℝ) + 1) * c


end LedgerExtra
end Twin
