-- Goldbach/GoldFunX.lean
--
-- An end-to-end Goldbach theorem for the canonical (Tenor-aligned) parallel FunX track.
-- This is the “no user-supplied witness” entry point: the analytic witness is built
-- internally from the Tenor FunX pipeline and the remaining analytic assumptions are
-- isolated as explicit axioms in the relevant `Cert/*` modules.

import Goldbach.CompleteTenorFunX_CanonBudget
import Goldbach.FiniteBase.CombineAll

namespace Goldbach

/-- Canonical end-to-end Goldbach theorem (parallel FunX track, `X0 = 1_000_000`). -/
theorem goldbach_funX_canon [Goldbach.BG_Calib.WeightsBridgeHyp] :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  have hBase : FiniteBaseUpTo 1_000_000 := Goldbach.FiniteBase.finiteBaseUpTo_1e6
  exact Goldbach.ParallelFunXCanon.goldbach_from_tenorFunX_fun_auto (hBase := hBase)

end Goldbach
