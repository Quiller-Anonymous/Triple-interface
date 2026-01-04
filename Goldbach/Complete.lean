-- Goldbach/Complete.lean
import Goldbach.CoreTypes
import Goldbach.FiniteBase.CombineAll
import Goldbach.Analytic.Hyp
import Goldbach.Analytic.Witness
import Goldbach.Final   -- contains `goldbach_final`
import Goldbach.AO_SigmaPos   -- sigma upper certificate (canonical instance)
import Goldbach.BG_CalibBridgeStub

open Goldbach

namespace Goldbach

/-- Conditional final theorem at the canonical cutoff `X0 = 1_000_000`. -/
theorem goldbach_from_hyp
  (A : Analytic.AnalyticHyp 1_000_000 10_000 1.0 0.05 0.01) :
  ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  -- finite base proven up to 1_000_000
  have hBase : FiniteBaseUpTo 1_000_000 := Goldbach.FiniteBase.finiteBaseUpTo_1e6
  exact goldbach_final (Analytic.toWitness A) (by simpa using hBase)

/--
Same as `goldbach_from_hyp`, but exposes the canonical sigma upper bound as an
explicit instance and allows threading a bridge certificate if available.
The extra class hypotheses are not used directly here but make the dependencies
fully explicit at the entry point.
-/
theorem goldbach_from_hyp_canon
  [Goldbach.AO_SigmaPos.SigmaUpperOnWindow] [Goldbach.BG_Calib.WeightsBridgeHyp]
  (A : Analytic.AnalyticHyp 1_000_000 10_000 1.0 0.05 0.01) :
  ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  have hBase : FiniteBaseUpTo 1_000_000 := Goldbach.FiniteBase.finiteBaseUpTo_1e6
  -- `SigmaUpperOnWindow` and `WeightsBridgeHyp` are available as instances here
  simpa using (goldbach_from_hyp (A := A))

end Goldbach
