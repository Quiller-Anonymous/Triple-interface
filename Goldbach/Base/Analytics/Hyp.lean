-- Goldbach/Analytic/Hyp.lean
import Goldbach.ClosureBridge   -- GlobalClosurePointwise / ClosurePointwise

namespace Goldbach.Analytic

open Goldbach.Bridge

/--
An “analytic hypothesis” package: once above `X0`, you have a global
pointwise closure statement on even windows `[X, X+H]` with parameters
`S`, `c0`, `ε`, together with the intended numeric side conditions.
-/
structure AnalyticHyp (X0 : ℕ) : Prop :=
  (H    : ℕ)
  (S    : ℝ)
  (c0   : ℝ)
  (ε    : ℝ)
  (hS   : 0 < S)
  (hc0  : 0 < c0)
  (hε   : ε < c0)
  (global : GlobalClosurePointwise X0 H S c0 ε)

end Goldbach.Analytic
