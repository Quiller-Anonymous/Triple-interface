import Goldbach.CoreTypes
import Mathlib.Data.Nat.Parity

open Goldbach

namespace Goldbach.FiniteBase

/-- Glue `[a,b]` with `[b+1,c]`. If your chunk windows are even-adjacent, use your
    `union_even_cover` variant instead. -/
lemma union_adjacent {a b c : ℕ}
  (h₁ : FiniteBaseOn a b) (h₂ : FiniteBaseOn (b+1) c) :
  FiniteBaseOn a c := by
  intro n hn hna hnc
  by_cases hnb : n ≤ b
  · exact h₁ n hn hna hnb
  ·
    have hb1 : b + 1 ≤ n := Nat.succ_le_of_lt (not_le.mp hnb)  -- 4.26-safe
    exact h₂ n hn hb1 hnc

/-!
Glue for the chunk layout we generated: windows touch on even boundaries, so the
gap at `b+1` is an odd number that we can ignore when `n` is even.
-/
lemma union_even_adjacent {a b c : ℕ}
  (hb_even : Even b)
  (h₁ : FiniteBaseOn a b) (h₂ : FiniteBaseOn (b+2) c) :
  FiniteBaseOn a c := by
  intro n hn hna hnc
  by_cases hnb : n ≤ b
  · exact h₁ n hn hna hnb
  ·
    -- n is even and larger than b, so it cannot be the odd number b+1
    have hb_lt : b < n := Nat.lt_of_not_ge hnb
    have hb1_le : b + 1 ≤ n := Nat.succ_le_of_lt hb_lt
    have hb1_ne : n ≠ b + 1 := by
      intro h
      have h_even_succ : Even (Nat.succ b) := by simpa [h] using hn
      have h_odd_b : Odd b := Nat.even_succ.mp h_even_succ
      exact hb_even.not_odd h_odd_b
    have hb1_lt : b + 1 < n := lt_of_le_of_ne hb1_le hb1_ne.symm
    have hb2_le : b + 2 ≤ n := Nat.succ_le_of_lt hb1_lt
    exact h₂ n hn hb2_le hnc

end Goldbach.FiniteBase
