import Goldbach.GoldFunX_OptionB_Gold

/-!
Goldbach/AxiomAuditGoldOptionB.lean
===================================

Axiom audit for the Option-B pipeline entry point (textbook major-arc boundary).

This is a diagnostic helper: it makes it easy to see (via `#print axioms`) exactly which
explicit axioms the Option-B pipeline entry point depends on.
-/

#check Goldbach.goldbach_funX_canon_optionB_gold
#print axioms Goldbach.goldbach_funX_canon_optionB_gold
