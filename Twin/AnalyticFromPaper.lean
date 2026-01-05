import Mathlib
import Twin.GoalAPI
import Twin.PaperParams
import Twin.SingularSeries
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger
import Twin.AnalyticCore
import Twin.CLSFromL2
import Twin.MajorArc.Pin
import Twin.MajorArc.SWUniform
import Twin.SW.Defs

noncomputable section
open scoped BigOperators

namespace Twin.AnalyticFromPaper
open Twin Twin.GoalAPI

/-- Concrete parameters from the paper. -/
def P : Params := Twin.PaperParams.P

/-!
This file is a *constructor* layer: it specifies what analytic data from the
paper must be supplied in order to instantiate the final Twin pipeline.

In particular, the minor-arc remainder `emin` and the desmoothing/prime-power
correction `eds` are not hard-coded here: they come from the analytic TI stack.
-/

/-- Analytic data for the minor arcs and desmoothing channels.

`l2_minor` is the L² “CLS” bound for the banked minor arcs; we derive the
linear CLS bound from it via `Twin.CLSFromL2.toCLS`.
`desmooth` is the windowed budget for the desmoothing/prime-power correction. -/
structure ErrorData where
  emin : ℕ → ℝ
  eds  : ℕ → ℝ
  l2_minor : Twin.CLSL2.Bound P emin
  desmooth : Twin.AnalyticCore.DesmoothBound P eds

/-- Derived CLS bound from the L² input. -/
theorem cls_bound (E : ErrorData) : Twin.AnalyticCore.CLSBound P E.emin :=
  Twin.CLSFromL2.toCLS (P := P) (e := E.emin) E.l2_minor

/-- Desmoothing/prime-power budget from the supplied data. -/
@[inline] def desmooth_bound (E : ErrorData) : Twin.AnalyticCore.DesmoothBound P E.eds :=
  E.desmooth

/-- Gate inequality obtained *from inputs*: CLS, desmoothing, and a smooth
major-arc estimate.  This has the "baseline-conditional" shape that we
eventually want, but for now it assumes the (still-unproved) major-arc package
interface exposed in `Twin.MajorArc.Pin`. -/
theorem gate_onWindow_of_SME
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : ErrorData)
  (sme  : Twin.MajorArc.SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : Twin.MajorArc.GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec)) :
  AnalyticCore.GateOnWindow P E.emin E.eds :=
by
  simpa using
    Twin.MajorArc.gate_onWindow_of_SME
      (P := P) (emin := E.emin) (eds := E.eds)
      (sme := sme) (spec := spec) (pkg := pkg)

end Twin.AnalyticFromPaper
