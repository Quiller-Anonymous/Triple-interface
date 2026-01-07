import Goldbach.GoldFunX

/-!
Goldbach/AxiomAuditGold.lean
============================

Axiom audit for the canonical Goldbach entrypoint.

This is a diagnostic helper: it makes it easy to see (via `#print axioms`) exactly which
explicit axioms the canonical theorem depends on.
-/

#check Goldbach.goldbach_funX_canon
#print axioms Goldbach.goldbach_funX_canon

