
import Mathlib
import Goldbach.AO_Core

namespace Goldbach.AO_Major

/-- Re-export the AO σ-model used in the ledger. -/
@[simp] noncomputable abbrev sigma : ℕ → ℝ := Goldbach.AO_Core.sigma

/-- Re-export the canonical AO ledger main term. -/
@[simp] noncomputable abbrev Mcanon : ℕ → ℕ → ℝ := Goldbach.AO_Core.Mcanon

@[simp] noncomputable abbrev weight_mass := Goldbach.AO_Core.weight_mass
@[simp] noncomputable abbrev errAO := Goldbach.AO_Core.errAO

end Goldbach.AO_Major
