-- Goldbach/AnalyticPointwise.lean
import Mathlib
import Goldbach.ClosureBridge
import Goldbach.Windows

namespace Goldbach.Analytic

/-- Packaged pointwise window-closure witness. -/
structure PointwiseWitness where
  X0N  : ℕ
  HN   : ℕ
  Sval : ℝ
  c0val : ℝ
  eps  : ℝ
  S_pos   : 0 < Sval
  c0_pos  : 0 < c0val
  eps_lt  : eps < c0val
  global  : Goldbach.Bridge.GlobalClosurePointwise X0N HN Sval c0val eps

namespace PointwiseWitness

/-- Aliases to match concise field names used elsewhere. -/
abbrev X0 (w : PointwiseWitness) : ℕ := w.X0N
abbrev H  (w : PointwiseWitness) : ℕ := w.HN
abbrev S  (w : PointwiseWitness) : ℝ := w.Sval
abbrev c0 (w : PointwiseWitness) : ℝ := w.c0val
abbrev ε  (w : PointwiseWitness) : ℝ := w.eps

/-- Evaluate the witness at `X ≥ w.X0`. -/
lemma closure_at {w : PointwiseWitness} {X : ℕ} (hX : w.X0 ≤ X) :
    Goldbach.Bridge.ClosurePointwise X w.H w.S w.c0 w.ε :=
  w.global hX

/-- From the witness alone: every even `N ≥ w.X0` has a representation. -/
lemma representable_large {w : PointwiseWitness} {N : ℕ}
    (hEven : Goldbach.Windows.IsEven N) (hX0 : w.X0 ≤ N) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  have hpt := closure_at (w := w) (X := N) hX0
  have hN : N ∈ Goldbach.Windows.EvenIn N w.H :=
    Goldbach.Windows.mem_EvenIn_self hEven
  exact Goldbach.Bridge.closurePointwise_to_rep hpt hN

/-- Helper constructor from a proven global closure property. -/
def of_global
    (X0 H : ℕ) (S c0 ε : ℝ)
    (hS : 0 < S) (hc0 : 0 < c0) (hε : ε < c0)
    (g : Goldbach.Bridge.GlobalClosurePointwise X0 H S c0 ε) :
    PointwiseWitness :=
  { X0N := X0, HN := H, Sval := S, c0val := c0, eps := ε
    , S_pos := hS, c0_pos := hc0, eps_lt := hε, global := g }

end PointwiseWitness
end Goldbach.Analytic
