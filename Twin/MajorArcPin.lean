/-
  Twin/MajorArcPin.lean
  The *only* analytic assumption left: the pinned major-arc lower bound.
  Everything else in the pipeline is formalized.
-/
import Mathlib
import Twin.GoalAPI
import Twin.AnalyticCore

noncomputable section

namespace Twin.MajorArcPin
open Twin Twin.GoalAPI

/-- Major-arc pinned lower bound (paper §7).
    This is the *single external axiom* the Twin pipeline depends on. -/
axiom gate_pointwise
  (P : Params) (emin eds : ℕ → ℝ) :
  AnalyticCore.GatePointwise P emin eds

-- still in Twin/MajorArcPin.lean
namespace MajorArcPin

@[inline] def gateCert (P : Params) (emin eds : ℕ → ℝ) :
    AnalyticCore.GatePointwise P emin eds :=
  gate_pointwise P emin eds

end MajorArcPin

end Twin.MajorArcPin
