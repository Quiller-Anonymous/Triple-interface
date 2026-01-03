-- Goldbach/Analytic/Witness.lean
import Goldbach.Final
import Goldbach.Analytic.Hyp

namespace Goldbach.Analytic

/-- Package an analytic hypothesis into the `PointwiseWitness` used by `goldbach_final`. -/
def toWitness
    {X0 H : ℕ} {S c0 ε : ℝ}
    (A : AnalyticHyp X0 H S c0 ε) : PointwiseWitness :=
{ X0 := X0, H := H, S := S, c0 := c0, eps := ε,
  S_pos := A.S_pos, c0_pos := A.c0_pos, eps_lt_c0 := A.eps_lt,
  global := by
    intro X hX
    refine ⟨A.S_pos, A.c0_pos, A.eps_lt, ?_⟩
    intro N hN
    exact A.bound (X := X) hX hN }

end Goldbach.Analytic
