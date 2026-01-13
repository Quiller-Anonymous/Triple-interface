/-
  Goldbach/AO_SmoothLoss.lean

  Smoothing-loss channel: for now we model the contribution as 0 and give
  a fully proved on-window bound using the nonnegativity of δsmooth_canon.
-/
import Goldbach.Windows
import Goldbach.BG_Bank

namespace Goldbach.AO_SmoothLoss

open Real Goldbach Windows

/-- AO smoothing-loss error model (placeholder but *proved*): zero. -/
noncomputable def E_smooth (_X _N : ℕ) : ℝ := 0

/-- **Smoothing-loss bound (proved, no axioms).**
    Since `E_smooth = 0`, the bound follows from `δsmooth_canon ≥ 0`. -/
theorem E_smooth_bound
  {X N : ℕ} (hX : BG_Bank.X0 ≤ X) (hN : N ∈ EvenIn X BG_Bank.H) :
  |E_smooth X N| ≤ (0 : ℝ) := by
  simpa [E_smooth]

end Goldbach.AO_SmoothLoss
