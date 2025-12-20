-- Goldbach/Analytic/Witness.lean
import Goldbach.Final
import Goldbach.Analytic.Hyp

namespace Goldbach.Analytic

def toWitness {X0 : ℕ} (A : AnalyticHyp X0) : PointwiseWitness :=
{ X0 := X0, H := A.H, S := A.S, c0 := A.c0, eps := A.ε,
  S_pos := A.hS, c0_pos := A.hc0, eps_lt_c0 := A.hε,
  global := by intro X hX; exact A.global hX }

end Goldbach.Analytic
