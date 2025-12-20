-- Goldbach/Complete.lean
import Goldbach.CoreTypes
import Goldbach.FiniteBase.CombineAll
import Goldbach.Analytic.Hyp
import Goldbach.Analytic.Witness
import Goldbach.Final   -- contains `goldbach_final`

open Goldbach

namespace Goldbach

/-- Conditional final theorem at the chosen `X0`. -/
theorem goldbach_from_hyp {X0 : ℕ} (hX0 : X0 ≤ 1_000_000) (A : Analytic.AnalyticHyp X0) :
  ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  -- finite base proven up to 1_000_000, shrink to your X0
  have hBase : FiniteBaseUpTo X0 :=
    Goldbach.FiniteBaseUpTo.mono Goldbach.FiniteBase.finiteBaseUpTo_1e6 hX0
  exact goldbach_final (Analytic.toWitness A) hBase

end Goldbach
