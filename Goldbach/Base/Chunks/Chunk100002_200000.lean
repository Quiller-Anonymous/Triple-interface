import Mathlib
import Goldbach.Base.FiniteBaseDefs
import Goldbach.FiniteBase.Generated_100002_200000

namespace Goldbach.Base.Chunks

open Goldbach.Base
open Goldbach.FiniteBase

theorem finiteBase_chunk100002_200000 : FiniteBaseOn 100002 200000 := by
  classical
  intro N hE hLo hHi
  let t := Goldbach.FiniteBase.Generated_100002_200000.table
  match t.get? N with
  | some pq =>
      -- `pq : ℕ × ℕ` produced by the generator; Lean-side proof objects are `decide`
      have hp : Nat.Prime pq.1 := by decide
      have hq : Nat.Prime pq.2 := by decide
      have hsum : pq.1 + pq.2 = N := by decide
      exact ⟨pq.1, pq.2, hp, hq, hsum⟩
  | none =>
      -- If your CSV fully covers [100002,200000] this case should be unreachable.
      -- Use the coverage lemma to show this case is impossible.
      have hcov := Goldbach.FiniteBase.Generated_100002_200000.table_covers N hLo hHi
      -- hcov : ∃ pq, Goldbach.FiniteBase.Generated_100002_200000.table.get? N = some pq
      cases hcov with pq hpq
      -- But we are in the `none` case, so this is a contradiction
      have : False := by
        rw [hpq] at *; contradiction
      exact False.elim this

end Goldbach.Base.Chunks
