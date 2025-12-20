Goldbach finite-base chunks
============================

- Source: Tools/data/witness_1e6.json (from Archive.zip)
- Partition: 100 contiguous N-intervals of width 10,000 each: [1..10_000], [10_001..20_000], ..., [990_001..1_000_000].
- Each JSON contains rows of the form {"n": even N, "p": prime, "q": prime} with p+q=n for that interval.
- Integrity: see sha256 values in the manifest.

Suggested pipeline
------------------
1) Quick check per chunk (IO mode):
   lake env lean --run Tools/CheckFiniteCert.lean -- goldbach_chunks/chunk_042.json 1000000

2) Emit a Lean module per chunk (pure mode):
   lake env lean --run Tools/EmitFiniteCert.lean -- goldbach_chunks/chunk_042.json Goldbach/FiniteBase/Chunks/Chunk042.lean

3) Combine chunks using `Goldbach.Base.FiniteBaseOn.union_even_cover` into `FiniteBaseUpTo 1_000_000`.
