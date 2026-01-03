-- WeightMassInstance.lean
import Mathlib
import Goldbach.BankParams
import Goldbach.AO_WeightMass

namespace Goldbach
namespace AO_OffDiag

/-- Interface: on the canonical window, the absolute mass of the weight is ≤ 1. -/
class WeightMassOnWindow : Prop where
  weight_mass_abs_le_one_on_window :
    ∀ {X : ℕ}, BankParams.X0 ≤ X → |Goldbach.AO_WeightMass.weight_mass X| ≤ (1 : ℝ)

/-- On the canonical window `X ≥ X0`, the AO weight mass has absolute value ≤ 1.
    For the normalized tent kernel in `AO_Core`, `weight_mass X` is definitionally `1.0`. -/
theorem weight_mass_abs_le_one_on_window_canon {X : ℕ} (hX : BankParams.X0 ≤ X) :
    |Goldbach.AO_WeightMass.weight_mass X| ≤ (1 : ℝ) := by
  norm_num [Goldbach.AO_WeightMass.weight_mass]

/-- Register the window-weight bound as the instance your code expects. -/
instance : WeightMassOnWindow where
  weight_mass_abs_le_one_on_window := by
    intro X hX; exact weight_mass_abs_le_one_on_window_canon (X:=X) hX

end AO_OffDiag
end Goldbach
