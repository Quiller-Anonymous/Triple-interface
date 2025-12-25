import Mathlib
import Goldbach.AnalyticPointwise
import Goldbach.ClosureBridge
import Goldbach.Windows
import Goldbach.Base.FiniteBaseDefs
import Goldbach.AO_OffDiag.SigmaTailEuler_Analytic

open Goldbach
open Goldbach.Analytic
open Goldbach.Bridge
open Goldbach.Base
open Goldbach.Windows

namespace Goldbach

/-- Final finite-conditional statement: small cases by finite base, large by analytics. -/
theorem goldbach_final (w : PointwiseWitness) (hBase : FiniteBaseUpTo w.X0) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → GoldbachRep N := by
  intro N hEven h4
  by_cases hSmall : N ≤ w.X0
  ·  -- small N via finite base
     exact hBase hEven h4 hSmall
  ·  -- large N via pointwise closure + bridge
     have hX  : w.X0 ≤ N := le_of_not_ge hSmall
     have hcl : ClosurePointwise N w.H w.S w.c0 w.ε := w.global hX
     -- turn `Even N` into your decidable window predicate
     have hEven' : IsEven N := isEven_of_even hEven
     -- build the required window membership
     have hWin   : N ∈ EvenIn N w.H := mem_EvenIn_self (N:=N) (H:=w.H) hEven'
     -- bridge to a representation
     exact closurePointwise_to_rep (N:=N) (H:=w.H) hcl hWin

end Goldbach
