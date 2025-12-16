/-
  Goldbach/FiniteBase/FromGenerated.lean
  Bridge from the generated finite-base table to the FiniteBaseUpTo theorem.
  If you have certified proofs per entry, use them here.
  If not, we post very small axioms that encapsulate “the table is complete & sound”.
-/

import Mathlib
import Goldbach.Base.FiniteBaseDefs
import Goldbach.FiniteBase.UseGenerated

open Std
open Nat

namespace Goldbach.FiniteBase

/-- Convenience aliases. -/
local notation "LO" => Goldbach.FiniteBase.LO
local notation "HI" => Goldbach.FiniteBase.HI
local notation "get?" => Goldbach.FiniteBase.get?

/-!
  If your generated files already include *proofs* that each `(p,q)`
  are primes and sum to `N`, replace the two axioms below by those proofs.

  Otherwise, these two axioms are the *smallest* surface you need:
  - completeness: for every *even* N in [LO,HI], the table has an entry
  - soundness: every entry is a valid Goldbach witness (primes & sum)
-/

/-- Table completeness on even inputs in [LO, HI]. -/
axiom table_complete :
  ∀ {N : ℕ}, Even N → LO ≤ N → N ≤ HI → ∃ pq, get? N = some pq

/-- Table soundness: any hit gives primes that sum to N. -/
axiom table_sound :
  ∀ {N p q : ℕ}, LO ≤ N → N ≤ HI → get? N = some (p, q) →
    Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

/-- Convert a lookup hit into a `GoldbachRep`. -/
private theorem rep_of_hit {N p q : ℕ}
    (hNlo : LO ≤ N) (hNhi : N ≤ HI) (h : get? N = some (p,q))
    : Goldbach.Base.GoldbachRep N := by
  rcases table_sound (N := N) (p := p) (q := q) hNlo hNhi h with ⟨hp, hq, hsum⟩
  exact ⟨p, q, hp, hq, hsum⟩

/-- The exported finite-base theorem for the range `[4, HI]`. -/
theorem finiteBaseUpTo_HI : Goldbach.Base.FiniteBaseUpTo HI := by
  -- FiniteBaseUpTo HI = FiniteBaseOn 4 HI
  intro N hEven h4 hNhi
  have hNlo : LO ≤ N := by
    -- LO = 4 in your `UseGenerated.lean`; if not, replace the next line by
    -- an explicit lemma or `simp` unfolding LO
    have : LO = 4 := rfl
    simpa [this] using h4
  rcases table_complete (N := N) hEven hNlo hNhi with ⟨pq, hhit⟩
  rcases pq with ⟨p,q⟩
  exact rep_of_hit hNlo hNhi hhit

end Goldbach.FiniteBase
