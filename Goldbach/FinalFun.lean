import Mathlib
import Goldbach.AnalyticPointwiseFun
import Goldbach.Base.FiniteBaseDefs
import Goldbach.Windows

open Goldbach
open Goldbach.Analytic
open Goldbach.Base
open Goldbach.Windows

namespace Goldbach

/--
Final finite-conditional statement (scale-dependent window width):
small cases by finite base, large by the analytic witness with window width `H N`.
-/
theorem goldbach_final_fun (w : PointwiseWitnessFun) (hBase : FiniteBaseUpTo w.X0) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → GoldbachRep N := by
  intro N hEven h4
  by_cases hSmall : N ≤ w.X0
  · exact hBase hEven h4 hSmall
  ·
    have hX : w.X0 ≤ N := le_of_not_ge hSmall
    have hcl : Goldbach.Bridge.ClosurePointwiseFun N w.H w.S w.c0 w.ε := w.global hX
    have hEven' : IsEven N := isEven_of_even hEven
    have hWin : N ∈ EvenIn N (w.H N) := mem_EvenIn_self (N := N) (H := w.H N) hEven'
    exact Goldbach.Bridge.closurePointwiseFun_to_rep (X := N) (H := w.H) hcl hWin

end Goldbach

