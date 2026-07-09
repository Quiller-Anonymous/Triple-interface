import Goldbach.Final
import Goldbach.Complete
import Goldbach.CompleteFun
import Goldbach.CompleteTenorFunX_CanonBudget
import Goldbach.GoldFunX

/-!
AxiomAuditGoldbach.lean
======================

On-demand axiom audit for the main Goldbach entry points.

This file is intentionally kept at the repository root (not under `Goldbach/`) so it does not
affect standard `lake build` targets or CI runtimes. Build it explicitly when you want to inspect
axiom dependencies.
-/

#check Goldbach.goldbach_final
#print axioms Goldbach.goldbach_final

#check Goldbach.goldbach_from_hyp
#print axioms Goldbach.goldbach_from_hyp

#check Goldbach.goldbach_from_hyp_canon
#print axioms Goldbach.goldbach_from_hyp_canon

#check Goldbach.goldbach_from_hyp_fun
#print axioms Goldbach.goldbach_from_hyp_fun

#check Goldbach.goldbach_from_hyp_fun_canon
#print axioms Goldbach.goldbach_from_hyp_fun_canon

#check Goldbach.ParallelFunXCanon.goldbach_from_tenorFunX_fun_auto
#print axioms Goldbach.ParallelFunXCanon.goldbach_from_tenorFunX_fun_auto

#check Goldbach.goldbach_funX_canon
#print axioms Goldbach.goldbach_funX_canon
