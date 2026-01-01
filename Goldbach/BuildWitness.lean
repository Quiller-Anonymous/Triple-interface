/-
BuildWitness: produce a global window-closure from an analytic hypothesis.

This version uses the bridge-ready `AnalyticHyp` (from AnalyticGlobal) and
feeds it directly to the `Bridge.GlobalClosurePointwise` layer, then wraps
it into `Analytic.PointwiseWitness`.
-/
import Mathlib
import Goldbach.AnalyticPointwise
import Goldbach.ClosureBridge
import Goldbach.AnalyticGlobal
import Goldbach.AO_Instantiate

namespace Goldbach.BuildWitness

open Goldbach
open Goldbach.Bridge          -- GlobalClosurePointwise
open Goldbach.Analytic        -- PointwiseWitness

/-- From an analytic hypothesis, produce the *bridge* global window-closure. -/
theorem the_global
  (X0 H : ℕ) (S c0 ε : ℝ)
  (hyp : Goldbach.AnalyticHyp X0 H S c0 ε) :
  Goldbach.Bridge.GlobalClosurePointwise X0 H S c0 ε := by
  -- Goal after `intro X hX` is the 4-way conjunction:
  --   0 < S ∧ 0 < c0 ∧ ε < c0 ∧ ∀ {N}, N ∈ EvenIn X H → (R N : ℝ)/S ≥ c0 - ε
  intro X hX
  refine And.intro hyp.S_pos (And.intro hyp.c0_pos (And.intro hyp.eps_lt ?win))
  -- now prove the window inequality uniformly in N
  intro N hN
  exact hyp.bound hX hN

/-- A canonical witness, parameterized by an analytic hypothesis at the standard constants. -/
noncomputable def canonical
  (hyp : Goldbach.AnalyticHyp (10^6) (10^4) (1.0) (0.05) (0.01)) :
  Goldbach.Analytic.PointwiseWitness :=
by
  classical
  -- Build the global-closure (bridge layer) from the analytic hypothesis.
  have g : Goldbach.Bridge.GlobalClosurePointwise (10^6) (10^4) (1.0) (0.05) (0.01) :=
    the_global (10^6) (10^4) (1.0) (0.05) (0.01) hyp
  -- Package it with positivity as a PointwiseWitness (Analytic layer).
  exact Goldbach.Analytic.PointwiseWitness.of_global
    (10^6) (10^4) (1.0) (0.05) (0.01)
    hyp.S_pos hyp.c0_pos hyp.eps_lt g

end Goldbach.BuildWitness
