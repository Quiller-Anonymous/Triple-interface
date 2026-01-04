/-
  Twin/TwinFinalize.lean
  Close the pipeline: from paper bricks to a window-level twin witness.
-/
import Mathlib
import Twin.PaperBricks
import Twin.TargetsFromBricks
import Twin.SingularSeries
import Twin.AnalyticPointwise
import Twin.Bridge

noncomputable section

namespace Twin.TwinFinalize

open Twin
open Twin.PaperBricks
open Twin.TargetsFromBricks

/-- The twin witness, given bricks and positivity of the truncated series. -/
noncomputable def witness_from_bricks
  {P : Twin.GoalAPI.Params} (b : Bricks P)
  (ss_pos : 0 < truncSingularSeries P.S)
  (_eps_pos : 0 < P.eps)
  (eps_lt_half : P.eps < (1 : ℝ) / 2)
  : Analytic.TwinWitness := by
  classical
  refine
  { H := P.H
  , X0 := P.X0
  , gamma := (1 : ℝ) / 10
  , sigmaS := 1
  , sigmaS_pos := by norm_num
  , deltaD := 1
  , deltaD_pos := by norm_num
  , largeX_local := ?_ }
  intro X hX
  have hmass :
      0 < Twin.Bridge.localizedTwinMass X P.H :=
    Twin.TargetsFromBricks.localizedTwinMass_pos_from_bricks
      (P := P) b ss_pos eps_lt_half (X := X) hX
  exact Twin.Bridge.existsTwin_of_mass_pos (X := X) (H := P.H) hmass

/-- Large-X windows contain a twin, from bricks + positivity. -/
theorem windows_largeX
  {P : Twin.GoalAPI.Params} (b : Bricks P)
  (ss_pos : 0 < truncSingularSeries P.S)
  (_eps_pos : 0 < P.eps)
  (eps_lt_half : P.eps < (1 : ℝ) / 2) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H := by
  intro X hX
  let w := witness_from_bricks (P := P) b ss_pos _eps_pos eps_lt_half
  exact w.largeX_local hX

end Twin.TwinFinalize
