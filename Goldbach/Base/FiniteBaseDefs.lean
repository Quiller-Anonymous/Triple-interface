import Mathlib

open Nat

namespace Goldbach.Base

def GoldbachRep (N : ℕ) : Prop :=
  ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

def FiniteBaseOn (lo hi : ℕ) : Prop :=
  ∀ ⦃N⦄, Even N → lo ≤ N → N ≤ hi → GoldbachRep N

def FiniteBaseUpTo (X : ℕ) : Prop := FiniteBaseOn 4 X

/-- Shrinking the upper bound preserves the property. -/
lemma FiniteBaseOn.mono_right {lo hi hi' : ℕ}
    (h : FiniteBaseOn lo hi) (hle : hi' ≤ hi) : FiniteBaseOn lo hi' := by
  intro N hN hlo hhi'
  exact h hN hlo (le_trans hhi' hle)

/-- Raising the lower bound preserves the property. -/
lemma FiniteBaseOn.mono_left {lo lo' hi : ℕ}
    (h : FiniteBaseOn lo hi) (hle : lo ≤ lo') : FiniteBaseOn lo' hi := by
  intro N hN hlo' hhi
  have hlo : lo ≤ N := le_trans hle hlo'
  exact h hN hlo hhi

/-- If `b` and `N` are even and `b < N`, then `b + 2 ≤ N`. -/
lemma even_lt_even_add_two {b N : ℕ} (hb : Even b) (hN : Even N) (h : b < N) :
    b + 2 ≤ N := by
  rcases hb with ⟨k, rfl⟩
  rcases hN with ⟨m, rfl⟩
  have hk : k < m := by
    have : 2 * k < 2 * m := by simpa [two_mul] using h
    exact Nat.lt_of_mul_lt_mul_left this
  have : 2 * (k + 1) ≤ 2 * m := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hk)
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using this

/-- Glue two verified even windows `[a,b]` and `[b+2,c]`. -/
lemma FiniteBaseOn.union_even_cover
    {a b c : ℕ} (ha : Even a) (hb : Even b) (hc : Even c)
    (hab : a ≤ b) (hbc : b + 2 ≤ c)
    (h₁ : FiniteBaseOn a b) (h₂ : FiniteBaseOn (b + 2) c) :
    FiniteBaseOn a c := by
  intro N hN hNa hNc
  by_cases hNb : N ≤ b
  · -- N ∈ [a, b]
    exact h₁ hN hNa hNb
  · -- N > b ⇒ (by parity) b+2 ≤ N, so N ∈ [b+2, c]
    have hbN : b < N := lt_of_not_ge hNb
    have hb2N : b + 2 ≤ N := even_lt_even_add_two hb hN hbN
    exact h₂ hN hb2N hNc

end Goldbach.Base
