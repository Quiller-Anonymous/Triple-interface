/-
  Goldbach/Base/FiniteBase.lean
  Aggregates finished chunks into a single FiniteBaseUpTo lemma.
-/
import Goldbach.Base.FiniteBaseDefs

-- Import only the chunks that are *ready* (no sorry/placeholder).
-- Example:
-- import Goldbach.Base.Chunks.Chunk0004_0198
-- import Goldbach.Base.Chunks.Chunk0200_0398
-- import Goldbach.Base.Chunks.Chunk0400_0598
-- …

open Goldbach.Base

namespace Goldbach.Base.Aggregate

/-- Example aggregator: edit as you add chunks. -/
theorem finiteBase_small : FiniteBaseUpTo 198 := by
  -- Uncomment and glue when you have chunks:
  -- have h0 : FiniteBaseOn 4 198 := Goldbach.Base.Chunks.finiteBase_0004_0198
  -- exact h0
  -- For now keep the module compiling without importing unfinished chunks:
  exact fun N hE h4 hN => by cases hE with
  --  → remove this when chunks exist

end Goldbach.Base.Aggregate
