/-
  Twin/PaperBricks.lean
  Math scaffolding for the last analytic steps (revised).
  No admits here: only definitions of the obligations you will later prove from the paper.
-/
import Mathlib
import Twin.GoalAPI
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger
import Twin.SingularSeries

noncomputable section
open scoped BigOperators

namespace Twin.PaperBricks

/-- The two n-indexed error components in the pointwise gate:
    • `emin`  : minor-arc contribution at `n`
    • `eds`   : desmoothing/prime-power correction at `n`
    The pin tail is handled *pointwise* via a uniform cap below. -/
structure ErrorPieces (P : Twin.GoalAPI.Params) where
  emin : ℕ → ℝ
  eds  : ℕ → ℝ

namespace ErrorPieces

variable {P : Twin.GoalAPI.Params}

/-- We will only use `|emin|` pointwise. -/
@[simp] def absEmin (E : ErrorPieces P) : ℕ → ℝ := fun n => |E.emin n|

end ErrorPieces

/-
  Obligations from the paper (pure math, to be discharged later):

  • `gate_major`:      pinned *window-sum* lower bound:
                       (1 - eps)·SS·(H+1) ≤ mass + windowSum emin + windowSum eds + tailcap·(H+1).
  • `cls_budget`:      window-summed budget for |emin|.
  • `desmooth_budget`: window-summed budget for eds.
-/
structure Bricks (P : Twin.GoalAPI.Params) where
  E : ErrorPieces P
  /-- Window-sum gate lower bound (uniform in X ≥ X0).
      This is the major-arc pinned lower bound after summing over `k=0..H`. -/
  gate_major :
    ∀ {X : ℕ}, P.X0 ≤ X →
      (1 - P.eps) * Twin.truncSingularSeries P.S * (P.H + 1)
        ≤ Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H E.emin
          + Twin.Ledger.windowSum X P.H E.eds
          + (P.eps * Twin.truncSingularSeries P.S) * (P.H + 1) / 3
  /-- CLS window-sum budget for the minor-arc piece. -/
  cls_budget :
    ∀ {X : ℕ}, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H (fun n => |E.emin n|)
        ≤ P.eps * Twin.truncSingularSeries P.S * (P.H + 1) / 3
  /-- Desmoothing / prime-power window-sum budget. -/
  desmooth_budget :
    ∀ {X : ℕ}, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H E.eds
        ≤ P.eps * Twin.truncSingularSeries P.S * (P.H + 1) / 3

end Twin.PaperBricks
