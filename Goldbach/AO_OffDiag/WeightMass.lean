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
    With the current bank normalization, `weight_mass X = (wScale X)^2` and `wScale X ≤ 1`. -/
theorem weight_mass_abs_le_one_on_window_canon {X : ℕ} (hX : BankParams.X0 ≤ X) :
    |Goldbach.AO_WeightMass.weight_mass X| ≤ (1 : ℝ) := by
  have hw : Goldbach.BG_Bank.wScale X ≤ 1 := Goldbach.BG_Bank.wScale_le_one X
  have hw0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
  -- `wScale^2 ≤ 1` since `0 ≤ wScale ≤ 1`.
  have hsq : (Goldbach.BG_Bank.wScale X) ^ 2 ≤ (1 : ℝ) := by
    have : (Goldbach.BG_Bank.wScale X) * (Goldbach.BG_Bank.wScale X) ≤ (1 : ℝ) * (1 : ℝ) :=
      mul_le_mul hw hw hw0 (by norm_num)
    simpa [pow_two] using this
  have hsq0 : 0 ≤ (Goldbach.BG_Bank.wScale X) ^ 2 := by
    have : 0 ≤ (Goldbach.BG_Bank.wScale X) * (Goldbach.BG_Bank.wScale X) :=
      mul_nonneg hw0 hw0
    simpa [pow_two] using this
  simpa [Goldbach.AO_WeightMass.weight_mass, abs_of_nonneg hsq0] using hsq

/-- Register the window-weight bound as the instance your code expects. -/
instance : WeightMassOnWindow where
  weight_mass_abs_le_one_on_window := by
    intro X hX; exact weight_mass_abs_le_one_on_window_canon (X:=X) hX

end AO_OffDiag
end Goldbach
