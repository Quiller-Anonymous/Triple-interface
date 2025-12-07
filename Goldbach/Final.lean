import Mathlib
import Goldbach.Base.FiniteBaseDefs
import Goldbach.ClosureBridge
import Goldbach.AnalyticPointwise

open scoped Real
open Goldbach Goldbach.Bridge Goldbach.Analytic Goldbach.Base

namespace Goldbach.Final

/--
Conditional final statement: given a pointwise witness of window-closure,
we get representations for all sufficiently large even `N`.
-/
theorem goldbach_conditional
    (w : Goldbach.Analytic.PointwiseWitness) :
    ∀ {N : ℕ}, Even N → max 4 w.X0 ≤ N → Goldbach.Base.GoldbachRep N := by
  intro N hE hN
  -- If your bridge lemma has a different name, swap it here:
  exact Goldbach.ClosureBridge.pointwise_to_rep
    (X0 := w.X0) (H := w.H) (S := w.S) (c0 := w.c0) (ε := w.ε)
    w.hS_pos w.hc0_pos w.hε_lt
    w.global
    hE hN

end Goldbach.Final
