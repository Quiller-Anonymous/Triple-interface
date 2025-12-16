/-
  Twin/Config.lean
  Central place to pin (H, X0, S, eps, err) for the Twin pipeline.
-/
import Mathlib
import Twin.SingularSeries
import Twin.PinnedLower

noncomputable section

namespace Twin.Config

/-- Example scaffold; replace `sorry?` values with your concrete choices as you’re ready. -/
def inputs
    (H X0 : ℕ) (S : Finset ℕ) (eps : ℝ)
    (err : ℕ → ℝ)
    (hSpos : 0 < Twin.truncSingularSeries S)
    (herr : ∀ {X}, X0 ≤ X → Twin.Ledger.windowSum X H err ≤ eps * Twin.truncSingularSeries S * (H+1))
    (eps_pos : 0 < eps) (eps_lt_half : eps < (1 : ℝ)/2)
  : Twin.PinnedLower.Inputs :=
{ H := H, X0 := X0, S := S, eps := eps, err := err,
  ss_pos := hSpos, err_budget := by intro X hX; simpa using herr (X := X) hX,
  eps_pos := eps_pos, eps_lt_half := eps_lt_half }

end Twin.Config
