/-
  Twin/Pipeline.lean
  End-to-end assembly: from the analytic bundle to an executable TwinWitness,
  and the final "twins in every large window" statement.
-/
import Mathlib
import Twin.AssembleFromGates
import Twin.BuildWitness
import Twin.PinnedLower
import Twin.Bridge

noncomputable section

namespace Twin.Pipeline

/-- Deterministically build the witness from the bundle of gates. -/
noncomputable def witnessFrom (b : Twin.AssembleFromGates.Bundle) : Twin.Analytic.TwinWitness :=
  let ap    := Twin.AssembleFromGates.toAssemble b
  let gates := Twin.PinnedLower.toGates b.i (assemble_pointwise := ap.assemble_pointwise)
  Twin.BuildWitness.build gates

/-- Final conditional statement: once the bundle is instantiated, the result follows. -/
theorem twins_in_all_large_windows (b : Twin.AssembleFromGates.Bundle) :
    ∀ {X : ℕ}, b.i.X0 ≤ X → Twin.ExistsTwinInWindow X b.i.H := by
  intro X hX
  exact (witnessFrom b).largeX_local (X := X) hX

end Twin.Pipeline
