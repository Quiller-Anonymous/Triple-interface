import Mathlib

/-!
Canonical scalar parameters for the Goldbach pipeline.

These are the *numerical regime* parameters used in the pointwise closure / witness layer.
Keeping them centralized makes it clear what must be renormalized when the σ-model or error
budgets are rescaled.
-/

namespace Goldbach.CanonParams

/-- Global scale parameter in the closure inequality. -/
abbrev S : ℝ := (1 : ℝ)

/-- The canonical error tolerance in the closure inequality. -/
abbrev ε : ℝ := (4e-4 : ℝ)

end Goldbach.CanonParams
