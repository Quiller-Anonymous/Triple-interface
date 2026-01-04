/-
  Twin/PaperBricks_Instance.lean
  Assemble `Bricks P` from the three analytic facts. No `sorry` here.
-/
import Mathlib
import Twin.GoalAPI
import Twin.PaperParams
import Twin.PaperBricks
import Twin.SingularSeries
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger
import Twin.AnalyticCore

noncomputable section

namespace Twin.PaperBricks_Instance
open Twin Twin.GoalAPI Twin.PaperBricks

/-- Concrete parameters. -/
def P : Params := Twin.PaperParams.P

/-- Pure algebra: turn a verified analytic bundle into `Bricks P`. -/
def bricks_of
    (emin eds : ℕ → ℝ)
    (cls  : Twin.AnalyticCore.CLSBound P emin)
    (desm : Twin.AnalyticCore.DesmoothBound P eds)
    (gate : Twin.AnalyticCore.GateOnWindow P emin eds) :
    Twin.PaperBricks.Bricks P :=
by
  classical
  -- Use the same `emin`/`eds` everywhere.
  let E : ErrorPieces P := { emin := emin, eds := eds }
  refine
  { E := E
  , gate_major     := ?g
  , cls_budget     := ?c
  , desmooth_budget:= ?d
  }
  · -- Gate: window-sum inequality with these `emin`/`eds`.
    intro X hX
    simpa [E] using gate.bound (X := X) hX
  · -- CLS window budget for `|emin|`.
    intro X hX
    simpa [E] using cls.bound (X := X) hX
  · -- Desmoothing window budget for `eds`.
    intro X hX
    simpa [E] using desm.bound (X := X) hX

end Twin.PaperBricks_Instance
