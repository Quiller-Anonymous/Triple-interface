/-
  Twin/TwinMain.lean
  Thin wrapper: expose a ready-to-use “large X ⇒ twin in window” theorem
  from the assembled pipeline.
-/
import Mathlib
import Twin.GoalAPI
import Twin.PaperParams
import Twin.PaperBricks
import Twin.TwinFinalize

noncomputable section

namespace Twin.Main

open Twin
open Twin.GoalAPI

/-- Shorthand for the concrete parameters. -/
def P  : GoalAPI.Params := Twin.PaperParams.P

/--
If the truncated singular series is positive and `0 < eps < 1/2`,
then every sufficiently large window (starting at `X ≥ P.X0`) contains a twin pair.
-/
theorem windows_largeX
  (b : Twin.PaperBricks.Bricks P)
  (ss_pos      : 0 < truncSingularSeries P.S)
  (eps_pos     : 0 < P.eps := by norm_num)
  (eps_lt_half : P.eps < (1 : ℝ) / 2 := by norm_num)
  : ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H := by
  intro X hX
  -- Call the finalizer's theorem directly with the current X.
  exact Twin.TwinFinalize.windows_largeX (P := P) b ss_pos eps_pos eps_lt_half (X := X) hX

/-- (Optional convenience) produce the assembled witness object directly. -/
noncomputable def witness
  (b : Twin.PaperBricks.Bricks P)
  (ss_pos      : 0 < truncSingularSeries P.S)
  (eps_pos     : 0 < P.eps := by norm_num)
  (eps_lt_half : P.eps < (1 : ℝ) / 2 := by norm_num)
  : Analytic.TwinWitness :=
  Twin.TwinFinalize.witness_from_bricks (P := P) b ss_pos eps_pos eps_lt_half

end Twin.Main
