-- Goldbach/Complete.lean
import Goldbach.CoreTypes
import Goldbach.FiniteBase.CombineAll
import Goldbach.Analytic.Hyp
import Goldbach.Analytic.Witness
import Goldbach.Final   -- contains `goldbach_final`

open Goldbach

namespace Goldbach

/-- Conditional final theorem at the canonical cutoff `X0 = 1_000_000`. -/
theorem goldbach_from_hyp
  (A : Analytic.AnalyticHyp 1_000_000 10_000 1.0 0.05 0.01) :
  ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  -- finite base proven up to 1_000_000
  have hBase : FiniteBaseUpTo 1_000_000 := Goldbach.FiniteBase.finiteBaseUpTo_1e6
  exact goldbach_final (Analytic.toWitness A) (by simpa using hBase)

end Goldbach
