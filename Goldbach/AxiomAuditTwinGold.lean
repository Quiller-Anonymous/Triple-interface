import Goldbach.TwinGold

/-!
Goldbach/AxiomAuditTwinGold.lean
================================

Axiom audit for the Goldbach-side Twin integration theorem.

This file intentionally lives under `Goldbach/` (not `Twin/`) to avoid import cycles:
`Goldbach` may import `Twin.*`, but `Twin` must not import `Goldbach.*`.
-/

#check Goldbach.TwinGold.twins_in_all_large_windows
#print axioms Goldbach.TwinGold.twins_in_all_large_windows

#check Goldbach.TwinGold.twins_in_all_large_windows_default
#print axioms Goldbach.TwinGold.twins_in_all_large_windows_default

#check Goldbach.TI.TwinInstance.ti_l2_minor
#check Goldbach.TI.TwinInstance.ti_desmooth
#check Goldbach.TI.TwinInstance.ti_pinned
#print axioms Goldbach.TI.TwinInstance.ti_pinned
