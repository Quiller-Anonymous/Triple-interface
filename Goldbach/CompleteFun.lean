-- Goldbach/CompleteFun.lean
import Goldbach.CoreTypes
import Goldbach.FiniteBase.CombineAll
import Goldbach.Analytic.Hyp
import Goldbach.Analytic.Witness
import Goldbach.AnalyticPointwiseFunCompat
import Goldbach.FinalFun
import Goldbach.AO_SigmaPos   -- sigma upper certificate (canonical instance)
import Goldbach.BG_CalibBridgeStub

open Goldbach

namespace Goldbach

/--
Conditional final theorem at the canonical cutoff `X0 = 1_000_000`,
using the *scale-dependent* final wrapper `goldbach_final_fun`.

At the moment this is just a compatibility layer: the supplied analytic hypothesis
still has a constant window width `H = 10_000`, so we convert the fixed-width witness
to a scale-dependent witness via `PointwiseWitness.toFun`.
-/
theorem goldbach_from_hyp_fun
  (A : Analytic.AnalyticHyp 1_000_000 10_000 1.0 0.05 0.01) :
  ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  have hBase : FiniteBaseUpTo 1_000_000 := Goldbach.FiniteBase.finiteBaseUpTo_1e6
  -- build the fixed-width witness, then coerce to the scale-dependent witness
  let wFixed : Goldbach.Analytic.PointwiseWitness := Analytic.toWitness A
  let wFun : Goldbach.Analytic.PointwiseWitnessFun := Goldbach.Analytic.PointwiseWitness.toFun wFixed
  exact goldbach_final_fun wFun (by simpa using hBase)

/--
Canonical wrapper exposing the sigma upper certificate and the bridge weight hypothesis
at the entry point.  The class arguments are available for downstream instantiations;
the proof itself reuses `goldbach_from_hyp_fun`.
-/
theorem goldbach_from_hyp_fun_canon
  [Goldbach.AO_SigmaPos.SigmaUpperOnWindow] [Goldbach.BG_Calib.WeightsBridgeHyp]
  (A : Analytic.AnalyticHyp 1_000_000 10_000 1.0 0.05 0.01) :
  ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  simpa using (goldbach_from_hyp_fun (A := A))

end Goldbach
