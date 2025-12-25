import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_SigmaModel

namespace Goldbach.AO_SigmaPos

open Real
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

-- Re-export the model names expected by downstream files:
abbrev c0 : ℝ := Goldbach.AO_SigmaModel.c0
noncomputable abbrev sigma0 : ℝ := Goldbach.AO_SigmaModel.sigma0
noncomputable abbrev sigma : ℕ → ℝ := Goldbach.AO_SigmaModel.sigma

lemma sigma0_pos : 0 < sigma0 := Goldbach.AO_SigmaModel.sigma0_pos

/-- Crude upper bound on `sigma` on the canonical window. -/
class SigmaUpperOnWindow where
  Cσ : ℝ
  Cσ_nonneg : 0 ≤ Cσ
  sigma_even_ub_on_window :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |sigma N| ≤ Cσ

/-- A safe constant upper bound: `Cσ = 0.06`. -/
instance : SigmaUpperOnWindow where
  Cσ := 0.06
  Cσ_nonneg := by norm_num
  sigma_even_ub_on_window := by
    intro X N hX hN
    -- sigma is constant sigma0
    simp [sigma, Goldbach.AO_SigmaModel.sigma, Goldbach.AO_SigmaModel.sigma0,
          Goldbach.AO_SigmaModel.c0, Goldbach.AO_SigmaModel.sigma_caps,
          Goldbach.AO_AssembleEnvelope.δAO]
    norm_num

/-- On the canonical window, `σ(N) ≥ σ₀` (trivial since σ is constant σ₀). -/
lemma sigma_even_lb_on_window :
  ∀ {X N : ℕ}, (10^6 : ℕ) ≤ X → N ∈ EvenIn X (10^4) → sigma N ≥ sigma0 := by
  intro X N _hX _hN
  simp [sigma, Goldbach.AO_SigmaModel.sigma]

end Goldbach.AO_SigmaPos
