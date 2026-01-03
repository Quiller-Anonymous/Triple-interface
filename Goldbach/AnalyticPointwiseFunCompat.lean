import Goldbach.AnalyticPointwise
import Goldbach.AnalyticPointwiseFun
import Goldbach.ClosureBridgeFunCompat

namespace Goldbach.Analytic

open Goldbach.Bridge

/-- View a fixed-width witness as a scale-dependent witness (with constant `H`). -/
noncomputable def PointwiseWitness.toFun (w : Goldbach.Analytic.PointwiseWitness) :
    Goldbach.Analytic.PointwiseWitnessFun :=
{ X0 := w.X0
  H := Goldbach.Bridge.constH w.H
  S := w.S
  c0 := w.c0
  eps := w.eps
  S_pos := w.S_pos
  c0_pos := w.c0_pos
  eps_lt_c0 := w.eps_lt_c0
  global := by
    intro X hX
    exact Goldbach.Bridge.closurePointwise_to_fun (w.global (X := X) hX) }

end Goldbach.Analytic

