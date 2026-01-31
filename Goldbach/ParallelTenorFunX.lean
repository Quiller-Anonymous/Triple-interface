import Goldbach.ParallelTenorFunXCore

/-!
Compatibility wrapper.

Historically `Goldbach/ParallelTenorFunX.lean` contained both:
- the *core* inner-swap interface used by the major-arc route, and
- a closure/witness construction layer.

The polished-gold major-arc work now depends only on the core interface; this file keeps the
original import path stable by re-exporting `Goldbach/ParallelTenorFunXCore.lean`.
-/
