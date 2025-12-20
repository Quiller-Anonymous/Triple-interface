import Goldbach.Base.FiniteBaseDefs

namespace Goldbach

open Goldbach.Base

/-- Re-export the base Goldbach representation. -/
@[simp, reducible] def GoldbachRep (n : ℕ) : Prop := Goldbach.Base.GoldbachRep n

/-- Re-export finite-base window. -/
@[simp, reducible] def FiniteBaseOn (a b : ℕ) : Prop := Goldbach.Base.FiniteBaseOn a b

/-- Finite base up to `B`: all even `n` with `4 ≤ n ≤ B`. -/
@[simp, reducible] def FiniteBaseUpTo (B : ℕ) : Prop := Goldbach.Base.FiniteBaseOn 4 B

/-- Shrink the bound. -/
lemma FiniteBaseUpTo.mono {B B' : ℕ} (h : FiniteBaseUpTo B) (h' : B' ≤ B) :
  FiniteBaseUpTo B' := by
  intro n hn h4 hnB'
  exact h hn h4 (le_trans hnB' h')

end Goldbach
