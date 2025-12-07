+/-
+  Goldbach/Base/Chunks/Chunk700002_800000.lean
+  Chunk: certifies Goldbach for even numbers in [700002, 800000].
+-/
+import Goldbach.Base.FiniteBaseDefs
+import Goldbach.FiniteBase.Generated
+
+open Goldbach.Base
+
+namespace Goldbach.Base.Chunks
+
+/--
+  Goldbach holds for every even `N` with `700002 ≤ N ≤ 800000`, using the
+  pre-generated witness table in `Goldbach.FiniteBase.Generated.table`.
+
+  This chunk is split out so it can be combined with later chunks via
+  `FiniteBaseOn.union_even_cover` without depending on a monolithic proof.
+-/
+theorem finiteBase_chunk700002_800000 : FiniteBaseOn 700002 800000 := by
+  intro N hE hlo hN
+  -- A computational witness: lookup `N` in the generated table and certify the primes.
+  have hWitness :
+      (Even N ∧ 700002 ≤ N ∧ N ≤ 800000) →
+        ∃ pq,
+          Goldbach.FiniteBase.Generated.table.get? N = some pq ∧
+          Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = N := by
+    native_decide
+  rcases hWitness ⟨hE, hlo, hN⟩ with ⟨⟨p, q⟩, _, hp, hq, hsum⟩
+  exact ⟨p, q, hp, hq, hsum⟩
+
+end Goldbach.Base.Chunks
