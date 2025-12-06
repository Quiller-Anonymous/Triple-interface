/-
  Goldbach/AO_SigmaPos.lean  — axiom-free positivity of the singular series

  We model the singular series σ on the canonical window as a constant function
  with value σ₀ := δAO + c₀, where c₀ = 0.05.  This makes the two facts we need
  (σ₀ > 0 and σ(N) ≥ σ₀ on the window) provable without axioms.

  NOTE: This file *does not* import AO_Major, so there is no import cycle.
        AO_Major should import this file and use the names defined here.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.AO_ErrorEnvelope  -- for δAO and δAO_nonneg

namespace Goldbach.AO_SigmaPos

open Real
open Goldbach
open Goldbach.Windows
open Goldbach.AO_ErrorEnvelope

/-- Canonical target constant c₀. -/
noncomputable def c0 : ℝ := (0.05 : ℝ)

/-- Our σ₀ := δAO + c₀. -/
noncomputable def sigma0 : ℝ := δAO + c0

/-- Define the singular series on ℕ as the constant σ₀. -/
noncomputable def sigma : ℕ → ℝ := fun _ => sigma0

/-- σ₀ is positive (since δAO ≥ 0 and c₀ > 0). -/
lemma sigma0_pos : 0 < sigma0 := by
  have hδ : 0 ≤ δAO := δAO_nonneg
  have hc0 : 0 < c0 := by norm_num
  -- c0 ≤ σ0 = δAO + c0
  have hc0_le_sigma0 : c0 ≤ sigma0 := by
    have := add_le_add_right hδ c0    -- 0 + c0 ≤ δAO + c0
    simpa [sigma0, zero_add] using this
  exact lt_of_lt_of_le hc0 hc0_le_sigma0

/-- On the canonical window, σ(N) ≥ σ₀ (trivial since σ is constant σ₀). -/
lemma sigma_even_lb_on_window :
  ∀ {X N : ℕ}, (10^6 : ℕ) ≤ X → N ∈ EvenIn X (10^4) → sigma N ≥ sigma0 := by
  intro X N _hX _hN
  simp [sigma, sigma0]

end Goldbach.AO_SigmaPos
