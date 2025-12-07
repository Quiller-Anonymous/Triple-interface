/-  Goldbach/Base/Chunks/Chunk200002_300000.lean
   Chunk: certifies Goldbach for even numbers in [200002, 300000]. -/
+import Goldbach.Base.FiniteBaseDefs
+import Goldbach.FiniteBase.Generated
+
+open Goldbach.Base
+
+namespace Goldbach.Base.Chunks
+
+/--
+  Goldbach holds for every even `N` with `200002 ≤ N ≤ 300000`, using the
+  pre-generated witness table in `Goldbach.FiniteBase.Generated.table`.
+
+  This chunk is split out so it can be combined with later chunks via
+  `FiniteBaseOn.union_even_cover` without depending on a monolithic proof.
+-/
+theorem finiteBase_chunk200002_300000 : FiniteBaseOn 200002 300000 := by
+  intro N hE hlo hN
+  -- A computational witness: lookup `N` in the generated table and certify the primes.
+  have hWitness :
+      (Even N ∧ 200002 ≤ N ∧ N ≤ 300000) →
+        ∃ pq,
+          Goldbach.FiniteBase.Generated.table.get? N = some pq ∧
+          Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = N := by
+    native_decide
+  rcases hWitness ⟨hE, hlo, hN⟩ with ⟨⟨p, q⟩, _, hp, hq, hsum⟩
+  exact ⟨p, q, hp, hq, hsum⟩
+
+end Goldbach.Base.Chunks
