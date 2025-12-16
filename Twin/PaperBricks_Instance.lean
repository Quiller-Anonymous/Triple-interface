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
import Twin.AnalyticFromPaper

noncomputable section

namespace Twin.PaperBricks_Instance
open Twin Twin.GoalAPI Twin.PaperBricks

/-- Concrete parameters. -/
def P : Params := Twin.PaperParams.P

/-- The three core analytic facts, sharing the same `emin`/`eds`. -/
structure AnalyticBundle : Type :=
  (emin : ℕ → ℝ)
  (eds  : ℕ → ℝ)
  (cls  : Twin.AnalyticCore.CLSBound P emin)
  (desm : Twin.AnalyticCore.DesmoothBound P eds)
  (gate : Twin.AnalyticCore.GatePointwise P emin eds)

/-- Pure algebra: turn a verified analytic bundle into `Bricks P`. -/
def bricks_of (A : AnalyticBundle) : Twin.PaperBricks.Bricks P :=
by
  classical
  -- Use the same `emin`/`eds` everywhere.
  let E : ErrorPieces P := { emin := A.emin, eds := A.eds }
  refine
  { E := E
  , gate_major_min := ?g
  , cls_budget     := ?c
  , desmooth_budget:= ?d
  }
  · -- Gate: pointwise inequality with these `emin`/`eds`.
    intro X hX k hk
    -- `A.gate.bound` has exactly the right shape; just rewrite `E`.
    simpa [E] using A.gate.bound (X := X) (k := k) hX hk
  · -- CLS window budget for `|emin|`.
    intro X hX
    simpa [E] using A.cls.bound (X := X) hX
  · -- Desmoothing window budget for `eds`.
    intro X hX
    simpa [E] using A.desm.bound (X := X) hX

/-- The actual bricks used by the pipeline, built from the paper theorems. -/
def bricks : Twin.PaperBricks.Bricks P :=
by
  -- Plug in the paper implementations; they already share `emin`/`eds`.
  let A : AnalyticBundle :=
  { emin := Twin.AnalyticFromPaper.emin
  , eds  := Twin.AnalyticFromPaper.eds
  , cls  := Twin.AnalyticFromPaper.cls_bound
  , desm := Twin.AnalyticFromPaper.desmooth_bound
  , gate := Twin.AnalyticFromPaper.gate_pointwise
  }
  exact bricks_of A

end Twin.PaperBricks_Instance
