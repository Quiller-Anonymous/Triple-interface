import Mathlib
import Goldbach.AnalyticPointwiseDirect
import Goldbach.Base.FiniteBaseDefs
import Goldbach.Windows

open Goldbach
open Goldbach.Analytic
open Goldbach.Base
open Goldbach.Windows

namespace Goldbach

/-- Final finite-conditional theorem for the direct lower-term witness route. -/
theorem goldbach_final_direct
    (w : PointwiseWitnessDirect) (hBase : FiniteBaseUpTo w.X0) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → GoldbachRep N := by
  intro N hEven h4
  by_cases hSmall : N ≤ w.X0
  · exact hBase hEven h4 hSmall
  ·
    have hX : w.X0 ≤ N := le_of_not_ge hSmall
    have hEven' : Goldbach.Windows.IsEven N := Goldbach.Windows.isEven_of_even hEven
    exact PointwiseWitnessDirect.representable_large (w := w) hEven' hX

end Goldbach
