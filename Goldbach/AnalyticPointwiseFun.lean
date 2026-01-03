import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.Base.FiniteBaseDefs
import Goldbach.ClosureBridgeFun

open Goldbach
open Goldbach.Windows
open Goldbach.Base

namespace Goldbach.Analytic

/--
Scale-dependent witness packaging: the window width is `H X` rather than a fixed natural.

This is meant to be a low-risk parallel to `Goldbach/AnalyticPointwise.lean`.
-/
structure PointwiseWitnessFun where
  X0   : ℕ
  H    : ℕ → ℕ
  S    : ℝ
  c0   : ℝ
  eps  : ℝ
  S_pos     : 0 < S
  c0_pos    : 0 < c0
  eps_lt_c0 : eps < c0
  /-- Global hypothesis: for every `X ≥ X0`, pointwise closure holds on window width `H X`. -/
  global :
    ∀ {X : ℕ}, X0 ≤ X →
      Goldbach.Bridge.ClosurePointwiseFun X H S c0 eps

@[simp] abbrev PointwiseWitnessFun.ε (w : PointwiseWitnessFun) : ℝ := w.eps

namespace PointwiseWitnessFun

/--
For every even `N ≥ w.X0`, we obtain a Goldbach representation.
This is a wrapper: apply the closure at `X := N` and note `N ∈ EvenIn N (H N)`.
-/
theorem representable_large
  (w : PointwiseWitnessFun) :
  ∀ {N : ℕ}, IsEven N → w.X0 ≤ N → GoldbachRep N := by
  intro N hEven hX0
  have hpt : Goldbach.Bridge.ClosurePointwiseFun N w.H w.S w.c0 w.eps :=
    w.global (X := N) hX0
  have hmem : N ∈ EvenIn N (w.H N) := Goldbach.Windows.mem_EvenIn_self hEven
  exact Goldbach.Bridge.closurePointwiseFun_to_rep (X := N) (H := w.H) hpt hmem

end PointwiseWitnessFun
end Goldbach.Analytic

