import Mathlib

namespace Goldbach.AO_WeightMass

/-!
AO weight mass.

This is kept separate from `Goldbach.AO_Core` so that off-diagonal modules can depend on
`weight_mass` without importing `AO_Core` (which is useful when refactoring AOI to make
`Mcanon` definitionally match a staged term).
-/

/-- Major-arc weight mass (ledger normalization = 1). -/
@[simp] def weight_mass (_X : ℕ) : ℝ := (1 : ℝ)

end Goldbach.AO_WeightMass

