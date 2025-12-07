diff --git a/Goldbach/Base/FiniteBase.lean b/Goldbach/Base/FiniteBase.lean
index 9876bab3d0a37496552f7d142305badd715d154c..509de02345499ad367057603bca58fcf0c057eb5 100644
--- a/Goldbach/Base/FiniteBase.lean
+++ b/Goldbach/Base/FiniteBase.lean
@@ -1,27 +1,244 @@
 /-
   Goldbach/Base/FiniteBase.lean
   Aggregates finished chunks into a single FiniteBaseUpTo lemma.
 -/
 import Goldbach.Base.FiniteBaseDefs
+import Goldbach.Base.Chunks.Chunk0004_100000
+import Goldbach.Base.Chunks.Chunk100002_200000
+import Goldbach.Base.Chunks.Chunk200002_300000
+import Goldbach.Base.Chunks.Chunk300002_400000
+import Goldbach.Base.Chunks.Chunk400002_500000
+import Goldbach.Base.Chunks.Chunk500002_600000
+import Goldbach.Base.Chunks.Chunk600002_700000
+import Goldbach.Base.Chunks.Chunk700002_800000
+import Goldbach.Base.Chunks.Chunk800002_900000
+import Goldbach.Base.Chunks.Chunk900002_1000000

 -- Import only the chunks that are *ready* (no sorry/placeholder).
 -- Example:
 -- import Goldbach.Base.Chunks.Chunk0004_0198
 -- import Goldbach.Base.Chunks.Chunk0200_0398
 -- import Goldbach.Base.Chunks.Chunk0400_0598
 -- …
+--
+-- Chunking guidance:
+-- * Each chunk module should expose a lemma of the shape
+--     `theorem finiteBase_chunkXXXX_YYYY : FiniteBaseOn XXXX YYYY := by …`
+--   where XXXX and YYYY are even bounds with YYYY ≥ XXXX and YYYY ≤ 1000000.
+-- * Bounds must be adjacent at even offsets: for consecutive chunks we need
+--   `YYYY + 2 = ZZZZ` so that `FiniteBaseOn.union_even_cover` can glue them.
+-- * After importing the finished chunk modules, you can aggregate them using
+--   repeated applications of `FiniteBaseOn.union_even_cover`, finally turning
+--   the combined `FiniteBaseOn 4 1000000` into `FiniteBaseUpTo 1000000`.
+--
+-- This file keeps the small-range witness in place while additional chunk
+-- proofs are generated and checked.

 open Goldbach.Base

 namespace Goldbach.Base.Aggregate

-/-- Example aggregator: edit as you add chunks. -/
-theorem finiteBase_small : FiniteBaseUpTo 198 := by
-  -- Uncomment and glue when you have chunks:
-  -- have h0 : FiniteBaseOn 4 198 := Goldbach.Base.Chunks.finiteBase_0004_0198
-  -- exact h0
-  -- For now keep the module compiling without importing unfinished chunks:
-  exact fun N hE h4 hN => by cases hE with
-  --  → remove this when chunks exist
+/--
+  First chunk in the aggregation: Goldbach holds on `[4, 100000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk0004_100000 : FiniteBaseOn 4 100000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk0004_100000
+
+/--
+  Second chunk in the aggregation: Goldbach holds on `[100002, 200000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk100002_200000 : FiniteBaseOn 100002 200000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk100002_200000
+
+/--
+  Third chunk in the aggregation: Goldbach holds on `[200002, 300000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk200002_300000 : FiniteBaseOn 200002 300000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk200002_300000
+
+/--
+  Fourth chunk in the aggregation: Goldbach holds on `[300002, 400000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk300002_400000 : FiniteBaseOn 300002 400000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk300002_400000
+
+/--
+  Fifth chunk in the aggregation: Goldbach holds on `[400002, 500000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk400002_500000 : FiniteBaseOn 400002 500000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk400002_500000
+
+/--
+  Sixth chunk in the aggregation: Goldbach holds on `[500002, 600000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk500002_600000 : FiniteBaseOn 500002 600000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk500002_600000
+
+/--
+  Seventh chunk in the aggregation: Goldbach holds on `[600002, 700000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk600002_700000 : FiniteBaseOn 600002 700000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk600002_700000
+
+/--
+  Eighth chunk in the aggregation: Goldbach holds on `[700002, 800000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk700002_800000 : FiniteBaseOn 700002 800000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk700002_800000
+
+/--
+  Ninth chunk in the aggregation: Goldbach holds on `[800002, 900000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk800002_900000 : FiniteBaseOn 800002 900000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk800002_900000
+
+/--
+  Tenth chunk in the aggregation: Goldbach holds on `[900002, 1000000]`.
+
+  This lemma re-exports the chunk proof so it can participate in a
+  `FiniteBaseOn.union_even_cover` fold as additional chunks are added.
+-/
+theorem finiteBase_chunk900002_1000000 : FiniteBaseOn 900002 1000000 := by
+  simpa using Goldbach.Base.Chunks.finiteBase_chunk900002_1000000
+
+/--
+  Aggregated coverage for even numbers up to 200000 by gluing the first two
+  chunks. Additional chunks can extend this lemma using
+  `FiniteBaseOn.union_even_cover`.
+-/
+theorem finiteBase_chunk0004_200000 : FiniteBaseOn 4 200000 := by
+  refine Goldbach.Base.FiniteBaseOn.union_even_cover (a := 4) (b := 100000) (c := 200000)
+    (ha := by decide) (hb := by decide) (hc := by decide)
+    (hab := by decide) (hbc := by decide) ?h1 ?h2
+  · simpa using finiteBase_chunk0004_100000
+  · simpa using finiteBase_chunk100002_200000
+
+/--
+  Aggregated coverage for even numbers up to 300000 by gluing the first three
+  chunks. Additional chunks can extend this lemma using
+  `FiniteBaseOn.union_even_cover`.
+-/
+theorem finiteBase_chunk0004_300000 : FiniteBaseOn 4 300000 := by
+  refine Goldbach.Base.FiniteBaseOn.union_even_cover (a := 4) (b := 200000) (c := 300000)
+    (ha := by decide) (hb := by decide) (hc := by decide)
+    (hab := by decide) (hbc := by decide) ?h1 ?h2
+  · simpa using finiteBase_chunk0004_200000
+  · simpa using finiteBase_chunk200002_300000
+
+/--
+  Aggregated coverage for even numbers up to 400000 by gluing the first four
+  chunks. Additional chunks can extend this lemma using
+  `FiniteBaseOn.union_even_cover`.
+-/
+theorem finiteBase_chunk0004_400000 : FiniteBaseOn 4 400000 := by
+  refine Goldbach.Base.FiniteBaseOn.union_even_cover (a := 4) (b := 300000) (c := 400000)
+    (ha := by decide) (hb := by decide) (hc := by decide)
+    (hab := by decide) (hbc := by decide) ?h1 ?h2
+  · simpa using finiteBase_chunk0004_300000
+  · simpa using finiteBase_chunk300002_400000
+
+/--
+  Aggregated coverage for even numbers up to 500000 by gluing the first five
+  chunks. Additional chunks can extend this lemma using
+  `FiniteBaseOn.union_even_cover`.
+-/
+theorem finiteBase_chunk0004_500000 : FiniteBaseOn 4 500000 := by
+  refine Goldbach.Base.FiniteBaseOn.union_even_cover (a := 4) (b := 400000) (c := 500000)
+    (ha := by decide) (hb := by decide) (hc := by decide)
+    (hab := by decide) (hbc := by decide) ?h1 ?h2
+  · simpa using finiteBase_chunk0004_400000
+  · simpa using finiteBase_chunk400002_500000
+
+/--
+  Aggregated coverage for even numbers up to 600000 by gluing the first six
+  chunks. Additional chunks can extend this lemma using
+  `FiniteBaseOn.union_even_cover`.
+-/
+theorem finiteBase_chunk0004_600000 : FiniteBaseOn 4 600000 := by
+  refine Goldbach.Base.FiniteBaseOn.union_even_cover (a := 4) (b := 500000) (c := 600000)
+    (ha := by decide) (hb := by decide) (hc := by decide)
+    (hab := by decide) (hbc := by decide) ?h1 ?h2
+  · simpa using finiteBase_chunk0004_500000
+  · simpa using finiteBase_chunk500002_600000
+
+/--
+  Aggregated coverage for even numbers up to 700000 by gluing the first seven
+  chunks. Additional chunks can extend this lemma using
+  `FiniteBaseOn.union_even_cover`.
+-/
+theorem finiteBase_chunk0004_700000 : FiniteBaseOn 4 700000 := by
+  refine Goldbach.Base.FiniteBaseOn.union_even_cover (a := 4) (b := 600000) (c := 700000)
+    (ha := by decide) (hb := by decide) (hc := by decide)
+    (hab := by decide) (hbc := by decide) ?h1 ?h2
+  · simpa using finiteBase_chunk0004_600000
+  · simpa using finiteBase_chunk600002_700000
+
+/--
+  Aggregated coverage for even numbers up to 800000 by gluing the first eight
+  chunks. Additional chunks can extend this lemma using
+  `FiniteBaseOn.union_even_cover`.
+-/
+theorem finiteBase_chunk0004_800000 : FiniteBaseOn 4 800000 := by
+  refine Goldbach.Base.FiniteBaseOn.union_even_cover (a := 4) (b := 700000) (c := 800000)
+    (ha := by decide) (hb := by decide) (hc := by decide)
+    (hab := by decide) (hbc := by decide) ?h1 ?h2
+  · simpa using finiteBase_chunk0004_700000
+  · simpa using finiteBase_chunk700002_800000
+
+/--
+  Aggregated coverage for even numbers up to 900000 by gluing the first nine
+  chunks. Additional chunks can extend this lemma using
+  `FiniteBaseOn.union_even_cover`.
+-/
+theorem finiteBase_chunk0004_900000 : FiniteBaseOn 4 900000 := by
+  refine Goldbach.Base.FiniteBaseOn.union_even_cover (a := 4) (b := 800000) (c := 900000)
+    (ha := by decide) (hb := by decide) (hc := by decide)
+    (hab := by decide) (hbc := by decide) ?h1 ?h2
+  · simpa using finiteBase_chunk0004_800000
+  · simpa using finiteBase_chunk800002_900000
+
+/--
+  Aggregated coverage for even numbers up to 1000000 by gluing all ten chunks.
+-/
+theorem finiteBase_chunk0004_1000000 : FiniteBaseOn 4 1000000 := by
+  refine Goldbach.Base.FiniteBaseOn.union_even_cover (a := 4) (b := 900000) (c := 1000000)
+    (ha := by decide) (hb := by decide) (hc := by decide)
+    (hab := by decide) (hbc := by decide) ?h1 ?h2
+  · simpa using finiteBase_chunk0004_900000
+  · simpa using finiteBase_chunk900002_1000000
+
+/--
+  Convenience alias turning the aggregated chunks into a `FiniteBaseUpTo`
+  result.
+-/
+theorem finiteBase_small : FiniteBaseUpTo 1000000 := by
+  simpa [FiniteBaseUpTo] using finiteBase_chunk0004_1000000

 end Goldbach.Base.Aggregate
