/-
  Twin/TwinFinalize.lean
  Close the pipeline: from paper bricks to a window-level twin witness.
-/
import Mathlib
import Twin.GoalAPI
import Twin.PaperParams
import Twin.PaperBricks
import Twin.TargetsFromBricks
import Twin.ErrorBudgetFromBricks
import Twin.SingularSeries

noncomputable section

namespace Twin.TwinFinalize

open Twin
open Twin.GoalAPI
open Twin.PaperParams
open Twin.PaperBricks
open Twin.TargetsFromBricks
open Twin.ErrorBudgetFromBricks

/-- Assemble the two GoalAPI obligations from the bricks for the *derived* params. -/
def P' (P : Params) (b : Bricks P) : Params :=
  withErr P (errFrom P b)

/-- The twin witness, given bricks and positivity of the truncated series. -/
noncomputable def witness_from_bricks
  {P : Params} (b : Bricks P)
  (ss_pos : 0 < truncSingularSeries P.S)
  (eps_pos : 0 < P.eps)
  (eps_lt_half : P.eps < (1 : ℝ) / 2)
  : Analytic.TwinWitness := by
  -- Build the two obligations for P' from the bricks:
  have hSN : SpectralNullOnWindow (P' P b) :=
    spectralNull_from_bricks (P := P) b
  have hEB : ErrorBudget (P' P b) :=
    errorBudget_from_bricks (P := P) b
  -- Package via the standard witness builder:
  exact
    witnessFromGoals (P := P' P b) ss_pos eps_pos eps_lt_half hSN hEB

/-- Large-X windows contain a twin, from bricks + positivity. -/
theorem windows_largeX
  {P : Params} (b : Bricks P)
  (ss_pos : 0 < truncSingularSeries P.S)
  (eps_pos : 0 < P.eps)
  (eps_lt_half : P.eps < (1 : ℝ) / 2) :
  ∀ {X : ℕ}, (P' P b).X0 ≤ X → ExistsTwinInWindow X (P' P b).H := by
  intro X hX
  let w := witness_from_bricks (P := P) b ss_pos eps_pos eps_lt_half
  exact w.largeX_local hX

end Twin.TwinFinalize
