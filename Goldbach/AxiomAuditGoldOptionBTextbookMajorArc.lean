import Goldbach.GoldFunX_OptionB_TextbookMajorArc

/-!
Goldbach/AxiomAuditGoldOptionBTextbookMajorArc.lean
====================================================

Axiom audit for the “textbook major-arc boundary” Option-B entry point.

This is a diagnostic helper: it makes it easy to see (via `#print axioms`) exactly which explicit
axioms the end-to-end theorem depends on once the project-shaped pinned major-arc cap is removed
from the import graph.
-/

#check Goldbach.goldbach_funX_canon_optionB_textbookMajorArc
#print axioms Goldbach.goldbach_funX_canon_optionB_textbookMajorArc

