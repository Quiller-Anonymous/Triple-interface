/-
  Goldbach/AnalyticPointwise.lean
  Analytic “shim” layer that packages a witness and uses the bridge.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.Base.FiniteBaseDefs
import Goldbach.ClosureBridge   -- one-way: Analytic depends on Bridge

open Goldbach
open Goldbach.Windows   -- IsEven, EvenIn, mem_EvenIn_self
open Goldbach.Base      -- GoldbachRep

namespace Goldbach.Analytic

/--
A packaged witness that, once we are above some cutoff `X0`, gives a
pointwise closure statement on the even window `[X, X+H]` with parameters
`S`, `c0`, `eps`.  The inequalities are included to reflect the intended
numerical regime; they are not used directly by the large-N wrapper proof.
-/
structure PointwiseWitness where
  X0   : ℕ
  H    : ℕ
  S    : ℝ
  c0   : ℝ
  eps  : ℝ
  S_pos      : 0 < S
  c0_pos     : 0 < c0
  eps_lt_c0  : eps < c0
  /-- Global hypothesis: for every `X ≥ X0`, the pointwise closure holds. -/
  global :
    ∀ {X : ℕ}, X0 ≤ X →
      Goldbach.Bridge.ClosurePointwise X H S c0 eps

@[simp] abbrev PointwiseWitness.ε (w : PointwiseWitness) : ℝ := w.eps

namespace PointwiseWitness

/--
For every even `N ≥ w.X0`, we obtain a Goldbach representation.
This is a pure wrapper: it takes the pointwise closure at `X := N`,
observes that `N` lies in its own even window, and appeals to the
bridge lemma.
-/
theorem representable_large
  (w : PointwiseWitness) :
  ∀ {N : ℕ}, IsEven N → w.X0 ≤ N → GoldbachRep N := by
  intro N hEven hX0
  -- pointwise closure at X := N from the global hypothesis
  have hpt : Goldbach.Bridge.ClosurePointwise N w.H w.S w.c0 w.eps :=
    w.global (X := N) hX0
  -- N is in its own even window
  have hmem : N ∈ EvenIn N w.H := Goldbach.Windows.mem_EvenIn_self hEven
  -- bridge: closure ⇒ representation at N
  exact Goldbach.Bridge.closurePointwise_to_rep hpt hmem

end PointwiseWitness
end Goldbach.Analytic
