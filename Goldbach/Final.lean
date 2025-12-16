import Mathlib
import Goldbach.Rep
import Goldbach.Windows
import Goldbach.ClosureBridge
import Goldbach.AnalyticPointwise
import Goldbach.Base.FiniteBaseDefs

open Goldbach
open Goldbach.Base
open Goldbach.Analytic
open Goldbach.Bridge

namespace Goldbach

/-- Finite-Conditional Goldbach: analytic witness + finite base up to `w.X0`. -/
theorem goldbach_conditional (w : PointwiseWitness) :
    FiniteBaseUpTo w.X0 →
    ∀ {N : ℕ}, Even N → 4 ≤ N → GoldbachRep N := by
  intro hBase N hEven h4
  by_cases hSmall : N ≤ w.X0
  · -- small range is discharged by the finite base hypothesis
    -- FiniteBaseUpTo X0 is `FiniteBaseOn 4 X0`
    exact hBase hEven h4 hSmall
  · -- large range: use the already-packaged pointwise witness
    have hX : w.X0 ≤ N := le_of_not_ge hSmall
    have hcl : ClosurePointwise N w.H w.S w.c0 w.ε :=
      w.global hX
    -- bridge to an actual Goldbach representation
    exact closurePointwise_to_rep hcl hEven

end Goldbach
