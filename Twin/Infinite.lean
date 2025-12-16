/-
  Twin/Infinite.lean
  From a TwinWitness (or from Analytic assumptions) to arbitrarily far windows
  that contain a twin pair.
-/
import Mathlib
import Twin.PipelineOnWindow
import Twin.Assumptions

namespace Twin.Infinite

/-- From a `TwinWitness`, there are twin pairs in windows starting arbitrarily far out. -/
theorem windows_unbounded_of_witness (w : Twin.Analytic.TwinWitness) :
    ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧ Twin.ExistsTwinInWindow X w.H := by
  intro N
  -- pick a start X beyond both N and w.X0
  refine ⟨Nat.max w.X0 N, ?_, ?_⟩
  · exact Nat.le_max_right _ _
  · exact w.largeX_local (X := Nat.max w.X0 N) (Nat.le_max_left _ _)

/-- Same corollary, derived directly from your Analytic assumptions. -/
theorem windows_unbounded_of_assumptions (A : Twin.Assumptions.Analytic) :
    ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧ Twin.ExistsTwinInWindow X A.H := by
  intro N
  -- build the witness mechanically, then reuse the previous theorem
  let w := Twin.Assumptions.Analytic.toWitness A
  exact windows_unbounded_of_witness w N

end Twin.Infinite
