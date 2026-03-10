import Mathlib
import Goldbach.AnalyticPointwiseScale
import Goldbach.Base.FiniteBaseDefs
import Goldbach.Windows

open Goldbach
open Goldbach.Analytic
open Goldbach.Base
open Goldbach.Windows

namespace Goldbach

/--
Final finite-conditional statement for the scale-sensitive witness route.

Small cases are handled by the finite base; large cases are handled by the scale-sensitive
pointwise witness evaluated at `X := N`.
-/
theorem goldbach_final_scale
    (w : PointwiseWitnessScale) (hBase : FiniteBaseUpTo w.X0) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → GoldbachRep N := by
  intro N hEven h4
  by_cases hSmall : N ≤ w.X0
  · exact hBase hEven h4 hSmall
  ·
    have hX : w.X0 ≤ N := le_of_not_ge hSmall
    have hEven' : Goldbach.Windows.IsEven N := Goldbach.Windows.isEven_of_even hEven
    exact PointwiseWitnessScale.representable_large (w := w) hEven' hX

end Goldbach
