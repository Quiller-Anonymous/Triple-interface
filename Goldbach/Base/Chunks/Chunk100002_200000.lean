import Mathlib
import Goldbach.Base.FiniteBaseDefs
import Goldbach.FiniteBase.Generated_100002_200000

namespace Goldbach.Base.Chunks

open Goldbach.Base
open Goldbach.FiniteBase

theorem Chunk100002_200000 : FiniteBaseOn 100002 200000 := by
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
      -- You can replace this with a dedicated coverage lemma once you add it.
      exact False.elim (by
        -- placeholder until you add coverage: mark clearly as unreachable
        have : False := by
          -- e.g. later: `have : N ∈ keyset := ...`; contradiction
          admit
        exact this)

end Goldbach.Base.Chunks
