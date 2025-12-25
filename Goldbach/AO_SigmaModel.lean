import Mathlib
import Goldbach.AO_EnvelopeCore

namespace Goldbach.AO_SigmaModel

open Goldbach
open Goldbach.AO_AssembleEnvelope

/-- Canonical target constant `c₀`. -/
def c0 : ℝ := (0.05 : ℝ)

/-- Default caps for the σ lower-bound model (all deltas set to 0). -/
def sigma_caps : Caps :=
{ δ_kernel := 0
, δ_mellin := 0
, δ_smooth := 0
, δ_off := 0
, δ_kernel_nonneg := by norm_num
, δ_mellin_nonneg := by norm_num
, δ_smooth_nonneg := by norm_num
, δ_off_nonneg := by norm_num }

/-- Our `σ₀ := δAO + c₀` (using the default caps). -/
noncomputable def sigma0 : ℝ := δAO sigma_caps + c0

/-- The σ model: constant function with value `σ₀`. -/
noncomputable def sigma (_N : ℕ) : ℝ := sigma0

lemma sigma0_pos : 0 < sigma0 := by
  have hδ : 0 ≤ δAO sigma_caps := δAO_nonneg sigma_caps
  have hc0 : 0 < c0 := by unfold c0; norm_num
  have hc0_le : c0 ≤ sigma0 := by
    have := add_le_add_right hδ c0
    simpa [sigma0, add_assoc, add_left_comm, add_comm] using this
  exact lt_of_lt_of_le hc0 hc0_le

end Goldbach.AO_SigmaModel
